module Name where
import Exprs
import Util
import Show

{- Naming conventions for internally-generated variables -}

-- Naming convention for testing equality two terms of the same type
typeFactorName tp = "==" ++ show tp

-- Naming convention for factor v=(v1,v2)
pairFactorName tp1 tp2 = "v=(" ++ show (TpArr tp1 tp2) ++ ")"

internalFactorName tm = "v=" ++ show tm

-- Naming convention for constructor factor
ctorFactorName :: Var -> [(Term, Type)] -> Type -> String
ctorFactorName x as tp = internalFactorName (TmVarG CtorVar x as tp)

-- FGG factor name for the default ctor rule
ctorFactorNameDefault :: Var -> [Type] -> Type -> String
ctorFactorNameDefault x as = ctorFactorName x (map (\ (i, a) -> (TmVarL (etaName x i) a, a)) (enumerate as))

-- Establishes naming convention for eta-expanding a constructor/global def.
etaName x i = "?" ++ x ++ show i

-- Returns the names of the args for a constructor
nameParams :: Var -> [Type] -> [Param]
nameParams x = zip (map (etaName x) [0..])

startName = "%start%"

-- Names used for de-/refunctionalization
applyName y = "%apply" ++ y ++ "%"
unfoldName y = "%unapply" ++ y ++ "%"
targetName = "%this%"
foldCtorName y i = "%fold" ++ y ++ "_" ++ show i ++ "%"
foldTypeName y = "%Fold" ++ y ++ "%"
unfoldTypeName y = "%Unfold" ++ y ++ "%"
unfoldCtorName y = "%unfold" ++ y ++ "%"
unfoldCtorArgName y i = "%unfold" ++ y ++ "_" ++ show i ++ "%"
unfoldCtorArgNames y n = [unfoldCtorArgName y i | i <- [0..n-1]]


-- Names used for affLin
affLinName x = '%' : x
tpUnitName = "%Unit%"
tmUnitName = "%unit%"
tmNothingName i = "%nothing" ++ show i ++ "%"
tmJustName i = "%just" ++ show i ++ "%"
tpMaybeName i = "%Maybe" ++ show i ++ "%"

-- Constructors and case-ofs for affLin-generated datatypes
tmNothing :: Int -> Term
tmNothing i = TmVarG CtorVar (tmNothingName i) [] (tpMaybe i)

tmJust :: Int -> Term -> Type -> Term
tmJust i tm tp = TmVarG CtorVar (tmJustName i) [(tm, tp)] (tpMaybe i)

tpMaybe i = TpVar (tpMaybeName i)

tmUnit = TmVarG CtorVar tmUnitName [] tpUnit
tpUnit = TpVar tpUnitName

tmElimMaybe :: Int -> Term -> Type -> Term -> (Var, Term) -> Type -> Term
tmElimMaybe i tm tp ntm (jx, jtm) tp' =
  TmCase tm (tpMaybeName i)
    [Case (tmNothingName i) [] ntm,
     Case (tmJustName i) [(jx, tp)] jtm] tp'

tmElimUnit :: Term -> Term -> Type -> Term
tmElimUnit utm tm tp = TmCase utm tpUnitName [Case tmUnitName [] tm] tp

unitCtors = [Ctor tmUnitName []]
maybeCtors i tp = [Ctor (tmNothingName i) [], Ctor (tmJustName i) [tp]]

