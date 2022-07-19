module Struct.Helpers where
import Struct.Exprs
import Util.Helpers
import Data.List

-- Gets the type of an elaborated term in O(1) time
typeof :: Term -> Type
typeof (TmVarL x tp) = tp
typeof (TmVarG gv x tis as tp) = tp
typeof (TmLam x tp tm tp') = TpArr tp tp'
typeof (TmApp tm1 tm2 tp2 tp) = tp
typeof (TmLet x xtm xtp tm tp) = tp
typeof (TmCase ctm y cs tp) = tp
typeof (TmAmb tms tp) = tp
typeof (TmFactor wt tm tp) = tp
typeof (TmProd am as) = TpProd am (snds as)
typeof (TmElimProd am tm ps tm' tp) = tp
typeof (TmEqs tms) = TpVar "Bool" []

-- Returns the index of the only non-underscore var
-- "let <_, _, x, _> in ..."  =>  index of x = 2
injIndex :: [Var] -> Int
injIndex = h . zip [0..] where
  h [] = -1
  h ((i, "_") : xs) = h xs
  h ((i, x) : xs) = i

-- Sorts cases according to the order they are appear in the datatype definition
-- This allows you to do case tm of C2->... | C1->..., which then gets translated to
-- case tm of C1->... | C2->... for ease of use internally
sortCases :: [Ctor] -> [CaseUs] -> [CaseUs]
sortCases ctors cases = snds $ sortBy (\ (a, _) (b, _) -> compare a b) (label cases) where
  getIdx :: Int -> Var -> [Ctor] -> Int
  getIdx i x [] = i + 1
  getIdx i x (Ctor x' tp : cs)
    | x == x' = i
    | otherwise = getIdx (succ i) x cs

  label = map $ \ c@(CaseUs x as tm) -> (getIdx 0 x ctors, c)

-- Returns the ctors to the left and to the right of one named x
-- (but discards the ctor named x itself)
splitCtorsAt :: [Ctor] -> Var -> ([Ctor], [Ctor])
splitCtorsAt [] x = ([], [])
splitCtorsAt (Ctor x' as : cs) x
  | x == x' = ([], cs)
  | otherwise =
    let (b, a) = splitCtorsAt cs x in
      (Ctor x' as : b, a)


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
  tp = typeof tm
  h [] = tm
  h ((x, xtm, xtp) : ds) = TmLet x xtm xtp (h ds) tp

-- Returns the amb branches, or just a singleton of the term if it is not TmAmb
splitAmbs :: Term -> [Term]
splitAmbs (TmAmb tms tp) = tms
splitAmbs tm = [tm]

-- Joins a list of terms into a TmAmb if there are != 1 branches
-- If there is only one branch, return it
joinAmbs :: [Term] -> Type -> Term
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
  foldr (\ (a, atp) tm -> TmLam a atp tm (typeof tm))
    (addArgs gv x tis tas vas y) vas

toArg :: Term -> Arg
toArg tm = (tm, typeof tm)

-- Maps toArg over a list of terms
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

-- Applies f to all the types in a list of ctors
mapCtorsM :: Monad m => (Type -> m Type) -> [Ctor] -> m [Ctor]
mapCtorsM f = mapM $ \ (Ctor x tps) -> pure (Ctor x) <*> mapM f tps

mapCtors :: (Type -> Type) -> [Ctor] -> [Ctor]
mapCtors f = map $ \ (Ctor x tps) -> Ctor x (map f tps)

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

