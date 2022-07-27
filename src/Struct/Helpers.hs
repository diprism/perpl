module Struct.Helpers where
import Struct.Exprs
import Util.None
import Util.Helpers
import Data.List
import Data.Foldable (traverse_)
import Control.Applicative (Alternative(empty))

-- Gets the type of an elaborated term in O(1) time
typeof :: Alternative dparams => Term dparams -> Type dparams
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
typeof (TmEqs tms) = tpBool

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
sortCases :: [Ctor dparams1] -> [CaseUs dparams2] -> [CaseUs dparams2]
sortCases ctors cases = snds $ sortBy (\ (a, _) (b, _) -> compare a b) (label cases) where
  getIdx :: Int -> Var -> [Ctor dparams] -> Int
  getIdx i x [] = i + 1
  getIdx i x (Ctor x' _tp : cs)
    | x == x' = i
    | otherwise = getIdx (succ i) x cs

  label = map $ \ c@(CaseUs x as tm) -> (getIdx 0 x ctors, c)

-- Returns the ctors to the left and to the right of one named x
-- (but discards the ctor named x itself)
splitCtorsAt :: [Ctor dparams] -> Var -> ([Ctor dparams], [Ctor dparams])
splitCtorsAt [] x = ([], [])
splitCtorsAt (Ctor x' as : cs) x
  | x == x' = ([], cs)
  | otherwise =
    let (b, a) = splitCtorsAt cs x in
      (Ctor x' as : b, a)


-- Splits tp1 -> tp2 -> ... -> tpn into ([tp1, tp2, ...], tpn)
splitArrows :: Type dparams -> ([Type dparams], Type dparams)
splitArrows (TpArr tp1 tp2) = let (tps, end) = splitArrows tp2 in (tp1 : tps, end)
splitArrows tp = ([], tp)

-- Joins ([tp1, tp2, ...], tpn) into tp1 -> tp2 -> ... -> tpn
joinArrows :: [Type dparams] -> Type dparams -> Type dparams
joinArrows tps end = foldr TpArr end tps

-- Splits tm1 tm2 tm3 ... tmn into (tm1, [(tm2, tp2), (tm3, tp3), ..., (tmn, tpn)])
splitApps :: Term dparams -> (Term dparams, [Arg dparams])
splitApps = splitAppsh []
  where
    splitAppsh :: [Arg dparams] -> Term dparams -> (Term dparams, [Arg dparams])
    splitAppsh acc (TmApp tm1 tm2 tp2 tp) =
      splitAppsh ((tm2, tp2) : acc) tm1
    splitAppsh acc tm = (tm, acc)

-- Joins (tm1, [tm2, tm3, ..., tmn]) into tm1 tm2 tm3 ... tmn
joinApps' :: Alternative dparams => Term dparams -> [Term dparams] -> Term dparams
joinApps' tm = h (toArg tm) where
  h :: (Term dparams, Type dparams) -> [Term dparams] -> Term dparams
  h (tm1, tp) [] = tm1
  h (tm1, TpArr tp2 tp) (tm2 : as) = h (TmApp tm1 tm2 tp2 tp, tp) as
  h (tm1, tp) (tm2 : as) = error "internal error: in joinApps', trying to apply to non-arrow type"

-- Joins (tm1, [(tm2, tp2), (tm3, tp3), ..., (tmn, tpn)]) into tm1 tm2 tm3 ... tmn
joinApps :: Alternative dparams => Term dparams -> [Arg dparams] -> Term dparams
joinApps tm as = joinApps' tm (fsts as)

-- splitApps, but for UsTms
splitUsApps :: UsTm dparams -> (UsTm dparams, [UsTm dparams])
splitUsApps = h [] where
  h as (UsApp tm1 tm2) = h (tm2 : as) tm1
  h as tm = (tm, as)

-- Splits \ x1 : tp1. \ x2 : tp2. ... \ xn : tpn. tm into ([(x1, tp1), (x2, tp2), ..., (xn, tpn)], tm)
splitLams :: Term dparams -> ([Param dparams], Term dparams)
splitLams (TmLam x tp tm tp') = let (ls, end) = splitLams tm in ((x, tp) : ls, end)
splitLams tm = ([], tm)

-- Joins ([(x1, tp1), (x2, tp2), ..., (xn, tpn)], tm) into \ x1 : tp1. \ x2 : tp2. ... \ xn : tpn. tm
joinLams :: Alternative dparams => [Param dparams] -> Term dparams -> Term dparams
joinLams as tm = fst $ foldr
  (\ (a, atp) (tm, tp) ->
    (TmLam a atp tm tp, TpArr atp tp))
  (toArg tm) as

-- Splits let x2 = tm2 in let x3 = tm3 in ... let xn = tmn in tm1 into ([(x2, tm2, tp2), (x3, tm3, tp3), ..., (xn, tmn, tpn)], tm1)
splitLets :: Term dparams -> ([(Var, Term dparams, Type dparams)], Term dparams)
splitLets (TmLet x xtm xtp tm tp) =
  let (ds, end) = splitLets tm in ((x, xtm, xtp) : ds, end)
splitLets tm = ([], tm)

-- Joins ([(x2, tm2, tp2), (x3, tm3, tp3), ..., (xn, tmn, tpn)], tm1) into let x2 = tm2 in let x3 = tm3 in ... let xn = tmn in tm1
joinLets :: Alternative dparams => [(Var, Term dparams, Type dparams)] -> Term dparams -> Term dparams
joinLets ds tm = h ds where
  tp = typeof tm
  h [] = tm
  h ((x, xtm, xtp) : ds) = TmLet x xtm xtp (h ds) tp

-- Returns the amb branches, or just a singleton of the term if it is not TmAmb
splitAmbs :: Term dparams -> [Term dparams]
splitAmbs (TmAmb tms tp) = tms
splitAmbs tm = [tm]

-- Joins a list of terms into a TmAmb if there are != 1 branches
-- If there is only one branch, return it
joinAmbs :: [Term dparams] -> Type dparams -> Term dparams
joinAmbs (tm : []) tp = tm
joinAmbs tms tp = TmAmb tms tp

-- Converts Params [(Var, Type)] to Args [(Term, Type)]
paramsToArgs :: [Param dparams] -> [Arg dparams]
paramsToArgs = map $ \ (a, atp) -> (TmVarL a atp, atp)

-- Turns a constructor into one with all its args applied
addArgs :: GlobalVar -> Var -> [Type dparams] -> [Arg dparams] -> [Param dparams] -> Type dparams -> Term dparams
addArgs gv x tis tas vas y =
  TmVarG gv x tis (tas ++ [(TmVarL a atp, atp) | (a, atp) <- vas]) y

-- Eta-expands a constructor with the necessary extra args
etaExpand :: Alternative dparams => GlobalVar -> Var -> [Type dparams] -> [Arg dparams] -> [Param dparams] -> Type dparams -> Term dparams
etaExpand gv x tis tas vas y =
  foldr (\ (a, atp) tm -> TmLam a atp tm (typeof tm))
    (addArgs gv x tis tas vas y) vas

toArg :: Alternative dparams => Term dparams -> Arg dparams
toArg tm = (tm, typeof tm)

-- Maps toArg over a list of terms
toArgs :: Alternative dparams => [Term dparams] -> [Arg dparams]
toArgs = map toArg

mapArgM :: (Applicative m, Alternative dparams2) => (Term dparams1 -> m (Term dparams2)) -> Arg dparams1 -> m (Arg dparams2)
mapArgM f (atm, _) = toArg <$> f atm

mapArg :: Alternative dparams2 => (Term dparams1 -> Term dparams2) -> Arg dparams1 -> Arg dparams2
mapArg f (atm, _) = toArg (f atm)

-- Maps over the terms in a list of args
mapArgs :: Alternative dparams2 => (Term dparams1 -> Term dparams2) -> [Arg dparams1] -> [Arg dparams2]
mapArgs = map . mapArg

mapArgsM :: (Applicative m, Alternative dparams2) => (Term dparams1 -> m (Term dparams2)) -> [Arg dparams1] -> m [Arg dparams2]
mapArgsM = traverse . mapArgM

mapParamM :: Applicative m => (Type dparams1 -> m (Type dparams2)) -> Param dparams1 -> m (Param dparams2)
mapParamM f (x, tp) = ((,) x) <$> f tp

mapParamsM :: Applicative m => (Type dparams1 -> m (Type dparams2)) -> [Param dparams1] -> m [Param dparams2]
mapParamsM = traverse . mapParamM

mapParam :: (Type dparams1 -> Type dparams2) -> Param dparams1 -> Param dparams2
mapParam f (x, tp) = (x, f tp)

mapParams :: (Type dparams1 -> Type dparams2) -> [Param dparams1] -> [Param dparams2]
mapParams = map . mapParam

-- Maps over the terms in a list of cases
mapCasesM :: Applicative m => (Var -> [Param dparams] -> Term dparams -> m (Term dparams)) -> [Case dparams] -> m [Case dparams]
mapCasesM f = traverse $ \ (Case x ps tm) -> (Case x ps) <$> f x ps tm

-- Applies f to all the types in a list of ctors
mapCtorsM :: Applicative m => (Type dparams1 -> m (Type dparams2)) -> [Ctor dparams1] -> m [Ctor dparams2]
mapCtorsM f = traverse $ \ (Ctor x tps) -> (Ctor x) <$> traverse f tps

mapCtorsM_ :: Applicative m => (Type dparams -> m a) -> [Ctor dparams] -> m ()
mapCtorsM_ f = traverse_ $ \ (Ctor x tps) -> traverse_ f tps

mapCtors :: (Type dparams1 -> Type dparams2) -> [Ctor dparams1] -> [Ctor dparams2]
mapCtors f = map $ \ (Ctor x tps) -> Ctor x (map f tps)

-- Maps over the terms in a Prog
mapProgM :: Applicative m => (Term None -> m (Term None)) -> Prog -> m Prog
mapProgM f (ProgFun x ps tm tp) =
  (\tm' -> ProgFun x ps tm' tp) <$> f tm
mapProgM mtm (ProgExtern x ps tp) =
  pure (ProgExtern x ps tp)
mapProgM mtm (ProgData y cs) =
  pure (ProgData y cs)

-- Maps over the terms in Progs
mapProgsM :: Applicative m => (Term None -> m (Term None)) -> Progs -> m Progs
mapProgsM f (Progs ps end) =
  Progs <$> traverse (mapProgM f) ps <*> f end

-- Built-in datatype Bool

tmUnit = TmProd Multiplicative []
tpUnit = TpProd Multiplicative []

tpBoolName = "Bool"
tmTrueName = "True"
tmFalseName = "False"

tpBool :: Alternative dparams => Type dparams
tpBool = TpData tpBoolName empty

tmTrue, tmFalse :: Alternative dparams => Term dparams
tmTrue = TmVarG CtorVar tmTrueName [] [] tpBool
tmFalse = TmVarG CtorVar tmFalseName [] [] tpBool

builtins :: [UsProg]
builtins = [
  UsProgData tpBoolName [] [Ctor tmFalseName [], Ctor tmTrueName []]
  ]

progBuiltins :: UsProgs -> UsProgs
progBuiltins (UsProgs ps end) =
  UsProgs (builtins ++ ps) end
