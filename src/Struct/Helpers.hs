{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
module Struct.Helpers where
import Struct.Exprs
import Util.Helpers ( fsts, snds )
import Data.List ( sortBy )

-- Gets the type of an elaborated term in O(1) time
typeof :: Term -> Type
typeof (TmVarL x tp) = tp
typeof (TmVarG gv x tgs tis as tp) = tp
typeof (TmLam x tp tm tp') = TpArr tp tp'
typeof (TmApp tm1 tm2 tp2 tp) = tp
typeof (TmLet x xtm xtp tm tp) = tp
typeof (TmCase ctm y cs tp) = tp
typeof (TmAmb tms tp) = tp
typeof (TmFactorDouble wt tm tp) = tp
typeof (TmFactorNat wt tm tp) = tp
typeof (TmFactorRatio wt tm tp) = tp
typeof (TmProd am as) = TpProd am (snds as)
typeof (TmElimMultiplicative tm ps    tm' tp) = tp
typeof (TmElimAdditive       tm n i p tm' tp) = tp
typeof (TmEqs tms) = tpBool

-- Sorts cases according to the order they are appear in the datatype definition
-- This allows you to do case tm of C2->... | C1->..., which then gets translated to
-- case tm of C1->... | C2->... for ease of use internally
sortCases :: [Ctor] -> [CaseUs] -> [CaseUs]
sortCases ctors cases = snds $ sortBy (\ (a, _) (b, _) -> compare a b) (label cases) where
  getIdx :: Int -> TmName -> [Ctor] -> Int
  getIdx i x [] = i + 1
  getIdx i x (Ctor x' tp : cs)
    | x == x' = i
    | otherwise = getIdx (succ i) x cs

  label = map $ \ c@(CaseUs x as tm) -> (getIdx 0 x ctors, c)

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
splitLets :: Term -> ([(TmVar, Term, Type)], Term)
splitLets (TmLet x xtm xtp tm tp) =
  let (ds, end) = splitLets tm in ((x, xtm, xtp) : ds, end)
splitLets tm = ([], tm)

-- Joins ([(x2, tm2, tp2), (x3, tm3, tp3), ..., (xn, tmn, tpn)], tm1) into let x2 = tm2 in let x3 = tm3 in ... let xn = tmn in tm1
joinLets :: [(TmVar, Term, Type)] -> Term -> Term
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
mapCasesM :: Monad m => (TmName -> [Param] -> Term -> m Term) -> [Case] -> m [Case]
mapCasesM f = mapM $ \ (Case x ps tm) -> pure (Case x ps) <*> f x ps tm

-- Applies f to all the types in a list of ctors
mapCtorsM :: Monad m => (Type -> m Type) -> [Ctor] -> m [Ctor]
mapCtorsM f = mapM $ \ (Ctor x tps) -> pure (Ctor x) <*> mapM f tps

mapCtorsM_ :: Monad m => (Type -> m a) -> [Ctor] -> m ()
mapCtorsM_ f = mapM_ $ \ (Ctor x tps) -> mapM_ f tps

mapCtors :: (Type -> Type) -> [Ctor] -> [Ctor]
mapCtors f = map $ \ (Ctor x tps) -> Ctor x (map f tps)

-- Maps over the terms in a Prog
mapProgM :: Monad m => (Term -> m Term) -> Prog -> m Prog
mapProgM f (ProgDefine x ps tm tp) =
  pure (ProgDefine x ps) <*> f tm <*> pure tp
mapProgM mtm (ProgExtern x ps tp) =
  pure (ProgExtern x ps tp)
mapProgM mtm (ProgData y cs) =
  pure (ProgData y cs)

-- Maps over the terms in Progs
mapProgsM :: Monad m => (Term -> m Term) -> Progs -> m Progs
mapProgsM f (Progs ps end) =
  pure Progs <*> mapM (mapProgM f) ps <*> f end

-- Built-in datatypes
tpZeroName :: TpName
tpZeroName = TpN "_Zero"
tpZero :: Type
tpZero = TpData tpZeroName [] []

tmUnit = TmProd Multiplicative []
tpUnit = TpProd Multiplicative []

tpBoolName :: TpName
tpBoolName = TpN "Bool"
tmTrueName :: TmName
tmTrueName = TmN "True"
tmFalseName :: TmName
tmFalseName = TmN "False"
tpBool :: Type
tpBool = TpData tpBoolName [] []
tmTrue :: Term
tmTrue = TmVarG GlCtor tmTrueName [] [] [] tpBool
tmFalse :: Term
tmFalse = TmVarG GlCtor tmFalseName [] [] [] tpBool

tmAddName :: TmName
tmAddName = TmN "_Add"
tpAdd :: Type
tpAdd = TpArr tpNat tpNat

tpNatName :: TpName
tpNatName = TpN "Nat"
tmZeroName :: TmName
tmZeroName = TmN "Zero"
tmSuccName :: TmName
tmSuccName = TmN "Succ"
tpNat :: Type
tpNat = TpData tpNatName [] []

additionGenerator :: UsTm -> UsTm -> UsTm
additionGenerator (UsVar val1) (UsVar val2) = UsLam val1 tpNat
  (UsLam val2 tpNat (UsCase (UsVar val1) [CaseUs (TmN "Zero") [] (UsVar val2),
                                          CaseUs (TmN "Succ") [TmV "m'"] (UsApp (UsVar (TmV "Succ")) (UsApp (UsApp (UsVar (tmNameToVar tmAddName)) (UsVar (TmV "m'"))) (UsVar val2)))]))
additionGenerator _ _ = UsFail NoTp

builtins :: [UsProg]
builtins = [
  UsProgData tpZeroName [] [],
  UsProgData tpBoolName [] [Ctor tmFalseName [], Ctor tmTrueName []],
  UsProgData tpNatName [] [Ctor tmZeroName [], Ctor tmSuccName [tpNat]],
  UsProgDefine tmAddName (additionGenerator (UsVar (TmV "m")) (UsVar (TmV "n"))) (TpArr tpNat tpAdd)
  ]

progBuiltins :: UsProgs -> UsProgs
progBuiltins (UsProgs ps end) =
  UsProgs (builtins ++ ps) end

-- Compose a lambda from a list of argument names and a body
joinUsLams :: [TmVar] -> UsTm -> UsTm
joinUsLams xs tail =
  case xs of
    x:xs -> UsLam x NoTp (joinUsLams xs tail)
    [] -> tail