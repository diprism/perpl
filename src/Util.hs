module Util where
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Exprs

type Map k v = Map.Map k v
type Set v = Set.Set v

fsts :: Functor f => f (a, b) -> f a
fsts = fmap fst

snds :: Functor f => f (a, b) -> f b
snds = fmap snd

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f (Left a) = Left (f a)
mapLeft f (Right c) = Right c

-- Creates a matrix of all possible combinations of two lists
kronecker :: [a] -> [b] -> [[(a, b)]]
kronecker as bs = [[(a, b) | b <- bs] | a <- as]

-- Calls a function for each possible combination of elements from two lists,
-- collecting into a list of results
kronwith :: (a -> b -> c) -> [a] -> [b] -> [c]
kronwith f as bs = [f a b | (a, b) <- concat (kronecker as bs)]

-- n-dimensional Kronecker product
kronall :: [[a]] -> [[a]]
kronall = foldr (\ vs ws -> [(v : xs) | v <- vs, xs <- ws ]) [[]]

-- kronall, but keeps track of the position (row, col) each element came from
kronpos :: [[a]] -> [[(Int, Int, a)]]
kronpos as = kronall [[(i, length as', a) | (i, a) <- enumerate as'] | as' <- as]

-- [a, b, c, ...] -> [(0, a), (1, b), (2, c), ...]
enumerate :: [a] -> [(Int, a)]
enumerate = zip [0..]

-- Argument-reordered version of maybe
maybe2 :: Maybe a -> b -> (a -> b) -> b
maybe2 m n j = maybe n j m

infixl 4 <**>
(<**>) :: Applicative f => f (a -> b -> c) -> f (a, b) -> f c
(<**>) = (<*>) . fmap uncurry

infixr 2 |?|
(|?|) :: Maybe a -> Maybe a -> Maybe a
Nothing |?| m_else = m_else
Just a |?| m_else = Just a

okay :: Monad m => m ()
okay = return ()

isDefVar :: GlobalVar -> Bool
isDefVar DefVar = True
isDefVar CtorVar = False

isCtorVar :: GlobalVar -> Bool
isCtorVar CtorVar = True
isCtorVar DefVar = False

-- Gets the type of an elaborated term in O(1) time
getType :: Term -> Type
getType (TmVarL x tp) = tp
getType (TmVarG gv x tis as tp) = tp
getType (TmLam x tp tm tp') = TpArr tp tp'
getType (TmApp tm1 tm2 tp2 tp) = tp
getType (TmLet x xtm xtp tm tp) = tp
getType (TmCase ctm y cs tp) = tp
getType (TmSamp d tp) = tp
getType (TmAmb tms tp) = tp
getType (TmProd am as) = TpProd am (snds as)
getType (TmElimProd am tm ps tm' tp) = tp
getType (TmEqs tms) = TpVar "Bool"

typeof = getType

-- "let <_, _, x, _> in ..."  =>  index of x = 2
injIndex :: [Var] -> Int
injIndex = h . zip [0..] where
  h [] = -1
  h ((i, "_") : xs) = h xs
  h ((i, x) : xs) = i

-- Sorts cases according to the order they are appear in the datatype definition
sortCases :: [Ctor] -> [CaseUs] -> [CaseUs]
sortCases ctors cases = snds $ sortBy (\ (a, _) (b, _) -> compare a b) (label cases) where
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

-- Joins (tm1, [tm2, tm3, ..., tmn]) into tm1 tm2 tm3 ... tmn
joinApps' :: Term -> [Term] -> Term
joinApps' tm = h (toArg tm) where
  h :: (Term, Type) -> [Term] -> Term
  h (tm1, tp) [] = tm1
  h (tm1, TpArr tp2 tp) (tm2 : as) = h (TmApp tm1 tm2 tp2 tp, tp) as
  h (tm1, tp) (tm2 : as) = error "internal error: in joinApps', trying to apply to non-arrow type"

-- Joins (tm1, [(tm2, tp2), (tm3, tp3), ..., (tmn, tpn)]) into tm1 tm2 tm3 ... tmn
joinApps :: Term -> [Arg] -> Term
joinApps tm as = joinApps' tm (fsts as)

-- splitApps, but for UsTms
splitUsApps :: UsTm -> (UsTm, [UsTm])
splitUsApps = h [] where
  h as (UsApp tm1 tm2) = h (tm2 : as) tm1
  h as tm = (tm, as)

-- Splits \ x1 : tp1. \ x2 : tp2. ... \ xn : tpn. tm into ([(x1, tp1), (x2, tp2), ..., (xn, tpn)], tm)
splitLams :: Term -> ([Param], Term)
splitLams (TmLam x tp tm tp') = let (ls, end) = splitLams tm in ((x, tp) : ls, end)
splitLams tm = ([], tm)

-- Joins ([(x1, tp1), (x2, tp2), ..., (xn, tpn)], tm) into \ x1 : tp1. \ x2 : tp2. ... \ xn : tpn. tm
joinLams :: [Param] -> Term -> Term
joinLams as tm = fst $ foldr
  (\ (a, atp) (tm, tp) ->
    (TmLam a atp tm tp, TpArr atp tp))
  (toArg tm) as

-- Splits let x2 = tm2 in let x3 = tm3 in ... let xn = tmn in tm1 into ([(x2, tm2, tp2), (x3, tm3, tp3), ..., (xn, tmn, tpn)], tm1)
splitLets :: Term -> ([(Var, Term, Type)], Term)
splitLets (TmLet x xtm xtp tm tp) =
  let (ds, end) = splitLets tm in ((x, xtm, xtp) : ds, end)
splitLets tm = ([], tm)

-- Joins ([(x2, tm2, tp2), (x3, tm3, tp3), ..., (xn, tmn, tpn)], tm1) into let x2 = tm2 in let x3 = tm3 in ... let xn = tmn in tm1
joinLets :: [(Var, Term, Type)] -> Term -> Term
joinLets ds tm = h ds where
  tp = getType tm
  h [] = tm
  h ((x, xtm, xtp) : ds) = TmLet x xtm xtp (h ds) tp

-- Returns the amb branches, or just a singleton of the term if it is not TmAmb
splitAmbs :: Term -> [Term]
splitAmbs (TmAmb tms tp) = tms
splitAmbs tm = [tm]

-- Joins a list of terms into a TmAmb if there are >= 2 branches
-- If there is only one branch, return it
-- If there are no branches, return fail
joinAmbs :: [Term] -> Type -> Term
joinAmbs [] tp = TmSamp DistFail tp
joinAmbs (tm : []) tp = tm
joinAmbs tms tp = TmAmb tms tp

-- Converts Params [(Var, Type)] to Args [(Term, Type)]
paramsToArgs :: [Param] -> [Arg]
paramsToArgs = map $ \ (a, atp) -> (TmVarL a atp, atp)

-- Turns a constructor into one with all its args applied
addArgs :: GlobalVar -> Var -> [Type] -> [Arg] -> [Param] -> Type -> Term
addArgs gv x tis tas vas y =
  TmVarG gv x tis (tas ++ [(TmVarL a atp, atp) | (a, atp) <- vas]) y

-- Eta-expands a constructor with the necessary extra args
etaExpand :: GlobalVar -> Var -> [Type] -> [Arg] -> [Param] -> Type -> Term
etaExpand gv x tis tas vas y =
  foldr (\ (a, atp) tm -> TmLam a atp tm (getType tm))
    (addArgs gv x tis tas vas y) vas

toArg :: Term -> Arg
toArg tm = (tm, getType tm)

toArgs :: [Term] -> [Arg]
toArgs = map toArg

mapArgM :: Monad m => (Term -> m Term) -> Arg -> m Arg
mapArgM f (atm, _) = f atm >>= return . toArg

mapArg :: (Term -> Term) -> Arg -> Arg
mapArg f (atm, _) = toArg (f atm)

mapArgs :: (Term -> Term) -> [Arg] -> [Arg]
mapArgs = map . mapArg

-- Maps over the terms in a list of args
mapArgsM :: Monad m => (Term -> m Term) -> [Arg] -> m [Arg]
mapArgsM = mapM . mapArgM

mapParamM :: Monad m => (Type -> m Type) -> Param -> m Param
mapParamM f (x, tp) = pure ((,) x) <*> f tp

mapParamsM :: Monad m => (Type -> m Type) -> [Param] -> m [Param]
mapParamsM = mapM . mapParamM

mapParam :: (Type -> Type) -> Param -> Param
mapParam f (x, tp) = (x, f tp)

mapParams :: (Type -> Type) -> [Param] -> [Param]
mapParams = map . mapParam

-- Maps over the terms in a list of cases
mapCasesM :: Monad m => (Var -> [Param] -> Term -> m Term) -> [Case] -> m [Case]
mapCasesM f = mapM $ \ (Case x ps tm) -> pure (Case x ps) <*> f x ps tm

mapCtorsM :: Monad m => (Type -> m Type) -> [Ctor] -> m [Ctor]
mapCtorsM f = mapM $ \ (Ctor x tps) -> pure (Ctor x) <*> mapM f tps

-- Maps over the terms in a Prog
mapProgM :: Monad m => (Term -> m Term) -> Prog -> m Prog
mapProgM f (ProgFun x ps tm tp) =
  pure (ProgFun x ps) <*> f tm <*> pure tp
mapProgM mtm (ProgExtern x ps tp) =
  pure (ProgExtern x ps tp)
mapProgM mtm (ProgData y cs) =
  pure (ProgData y cs)

-- Maps over the terms in Progs
mapProgsM :: Monad m => (Term -> m Term) -> Progs -> m Progs
mapProgsM f (Progs ps end) =
  pure Progs <*> mapM (mapProgM f) ps <*> f end

-- Concats a list of lists, adding a delimiter
-- Example: delimitWith ", " ["item 1", "item 2", "item 3"] = "item 1, item 2, item 3"
delimitWith :: [a] -> [[a]] -> [a]
delimitWith del [] = []
delimitWith del [as] = as
delimitWith del (h : t) = h ++ del ++ delimitWith del t

-- Collects duplicates, counting how many
-- collectDups ['a', 'b', 'c', 'b', 'c', 'b'] = [('a', 1), ('b', 3), ('c', 2)]
collectDups :: Ord a => [a] -> [(a, Int)]
collectDups =
  Map.toList . foldr (Map.alter $ Just . maybe 1 succ) Map.empty
