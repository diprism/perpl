module Util where
import Data.List
import Exprs

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f (Left a) = Left (f a)
mapLeft f (Right c) = Right c

-- Creates a matrix of all possible combinations of two lists
kronecker :: [a] -> [b] -> [[(a, b)]]
kronecker as bs = map (\ a -> map (\ b -> (a, b)) bs) as

kronwith :: (a -> b -> c) -> [a] -> [b] -> [c]
kronwith f as bs = map (uncurry f) $ concat $ kronecker as bs

kronall :: [[a]] -> [[a]]
kronall = foldr (\ vs ws -> [ (v : xs) | v <- vs, xs <- ws ]) [[]]

kronpos :: [[a]] -> [[(Int, Int, a)]]
kronpos = kronall . map (\ as -> map (\ (i, a) -> (i, length as, a)) (enumerate as))

enumerate :: [a] -> [(Int, a)]
enumerate = zip [0..]

weightsRow :: Num n => Int {- Index -} -> Int {- Length -} -> [n]
weightsRow i l = [if j == i then 1 else 0 | j <- [0..l-1]] --map (\ j -> if j == i then 1 else 0) [0..l-1]

-- Argument-reordered version of maybe
maybe2 :: Maybe a -> b -> (a -> b) -> b
maybe2 m n j = maybe n j m

okay :: Monad m => m ()
okay = return ()

plus_l :: Num a => a -> [a] -> [a]
a `plus_l` as = map ((+) a) as


{- -- Concatenates a list of lists, returning that and a
-- list mapping original positions to their new indices
-- within the concatenated list
combine :: [[a]] -> ([a], [[Int]])
combine as =
  (concat as,
   foldr (\ as' is i -> [i..i + length as' - 1] : is (i + length as'))
     (const []) as 0)-}


-- Gets the type of an elaborated term in O(1) time
getType :: Term -> Type
getType (TmVarL x tp) = tp
getType (TmVarG gv x as tp) = tp
getType (TmLam x tp tm tp') = TpArr tp tp'
getType (TmApp tm1 tm2 tp2 tp) = tp
getType (TmLet x xtm xtp tm tp) = tp
getType (TmCase ctm ctp cs tp) = tp
getType (TmSamp d tp) = tp
getType (TmAmb tms tp) = tp

sortCases :: [Ctor] -> [CaseUs] -> [CaseUs]
sortCases ctors cases = map snd $ sortBy (\ (a, _) (b, _) -> compare a b) (label cases) where
  getIdx :: Int -> Var -> [Ctor] -> Int
  getIdx i x [] = i + 1
  getIdx i x (Ctor x' tp : cs)
    | x == x' = i
    | otherwise = getIdx (succ i) x cs

  label = map $ \ (CaseUs x as tm) -> (getIdx 0 x ctors, CaseUs x as tm)


-- Splits tp1 -> tp2 -> ... -> tpn into ([tp1, tp2, ...], tpn)
splitArrows :: Type -> ([Type], Type)
splitArrows (TpArr tp1 tp2) = let (tps, end) = splitArrows tp2 in (tp1 : tps, end)
splitArrows tp = ([], tp)

-- Joins ([tp1, tp2, ...], tpn) into tp1 -> tp2 -> ... -> tpn
joinArrows :: [Type] -> Type -> Type
joinArrows tps end = foldr TpArr end tps

-- Splits tm1 tm2 tm3 ... tmn into (tm1, [(tm2, tp2), (tm3, tp3), ..., (tmn, tpn)])
splitApps :: Term -> (Term, [Arg])
splitApps = splitAppsh []
  where
    splitAppsh :: [Arg] -> Term -> (Term, [Arg])
    splitAppsh acc (TmApp tm1 tm2 tp2 tp) =
      splitAppsh ((tm2, tp2) : acc) tm1
    splitAppsh acc tm = (tm, acc)

joinApps' :: Term -> [Term] -> Term
joinApps' tm = h (tm, getType tm) where
  h :: (Term, Type) -> [Term] -> Term
  h (tm1, tp) [] = tm1
  h (tm1, TpArr tp2 tp) (tm2 : as) = h (TmApp tm1 tm2 tp2 tp, tp) as
  h (tm1, tp) (tm2 : as) = error "internal error: in joinApps', trying to apply to non-arrow type"

joinApps :: Term -> [Arg] -> Term
joinApps tm as = joinApps' tm (map fst as)

splitUsApps :: UsTm -> (UsTm, [UsTm])
splitUsApps = h [] where
  h as (UsApp tm1 tm2) = h (tm2 : as) tm1
  h as tm = (tm, as)

joinLams :: [Param] -> Term -> Term
joinLams as tm = fst $ foldr
  (\ (a, atp) (tm, tp) ->
    (TmLam a atp tm tp, TpArr atp tp))
  (tm, getType tm) as

splitLams :: Term -> ([Param], Term)
splitLams (TmLam x tp tm tp') = let (ls, end) = splitLams tm in ((x, tp) : ls, end)
splitLams tm = ([], tm)

joinLets :: [(Var, Term, Type)] -> Term -> Term
joinLets ds tm = h ds where
  tp = getType tm
  h [] = tm
  h ((x, xtm, xtp) : ds) = TmLet x xtm xtp (h ds) tp

splitLets :: Term -> ([(Var, Term, Type)], Term)
splitLets (TmLet x xtm xtp tm tp) =
  let (ds, end) = splitLets tm in ((x, xtm, xtp) : ds, end)
splitLets tm = ([], tm)

paramsToArgs :: [Param] -> [Arg]
paramsToArgs = map $ \ (a, atp) -> (TmVarL a atp, atp)

-- Turns a constructor into one with all its args applied
addArgs :: GlobalVar -> Var -> [Arg] -> [Param] -> Type -> Term
addArgs gv x tas vas y =
  TmVarG gv x (tas ++ map (\ (a, atp) -> (TmVarL a atp, atp)) vas) y

-- Eta-expands a constructor with the necessary extra args
etaExpand :: GlobalVar -> Var -> [Arg] -> [Param] -> Type -> Term
etaExpand gv x tas vas y =
  foldr (\ (a, atp) tm -> TmLam a atp tm (getType tm))
    (addArgs gv x tas vas y) vas

-- Maps over the terms in a list of args
mapArgsM :: Monad m => (Term -> m Term) -> [Arg] -> m [Arg]
mapArgsM f = mapM $ \ (atm, atp) -> pure (,) <*> f atm <*> pure atp

-- Maps over the terms in a list of cases
mapCasesM :: Monad m => ([Param] -> Term -> m Term) -> [Case] -> m [Case]
mapCasesM f = mapM $ \ (Case x ps tm) -> pure (Case x ps) <*> f ps tm

-- Maps over the terms in a Prog
mapProgM :: Monad m => (Term -> m Term) -> Prog -> m Prog
mapProgM f (ProgFun x ps tm tp) =
  pure (ProgFun x ps) <*> f tm <*> pure tp
mapProgM mtm (ProgExtern x xp ps tp) =
  pure (ProgExtern x xp ps tp)
mapProgM mtm (ProgData y cs) =
  pure (ProgData y cs)

-- Maps over the terms in Progs
mapProgsM :: Monad m => (Term -> m Term) -> Progs -> m Progs
mapProgsM f (Progs ps end) =
  pure Progs <*> mapM (mapProgM f) ps <*> f end
