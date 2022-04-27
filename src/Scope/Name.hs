module Scope.Name where
import Struct.Lib
import Util.Helpers

{- Naming conventions for internally-generated variables -}

-- Naming convention for testing equality two terms of the same type
typeFactorName tp = "==" ++ show tp

eqFactorName tp n = "[" ++ show n ++ "]" ++ "==" ++ show tp

-- Naming convention for factor v=(v1,v2)
pairFactorName tp1 tp2 = "v=(" ++ show (TpArr tp1 tp2) ++ ")"

ampFactorName :: [Type] -> Int -> String
--ampFactorName i tps = "v=" ++ show (TpAmp tps) ++ "." ++ show i
ampFactorName tps i = "v=<" ++ delimitWith ", " [show tp | tp <- tps] ++ ">." ++ show i

prodFactorName' tps = "v=(" ++ delimitWith ", " tps ++ ")"
prodFactorName tps = prodFactorName' (map show tps)

--prodValName' :: [String] -> String
prodValName' tms = "(" ++ delimitWith ", " tms ++ ")"
--prodValName :: Show x => [x] -> String
prodValName xs = prodValName' (map show xs)

internalFactorName tm = "v=" ++ show tm

-- Naming convention for constructor factor
ctorFactorName :: Var -> [(Term, Type)] -> Type -> String
ctorFactorName x as tp = internalFactorName (TmVarG CtorVar x [] as tp)

-- FGG factor name for the default ctor rule
ctorFactorNameDefault :: Var -> [Type] -> Type -> String
ctorFactorNameDefault x as = ctorFactorName x [(TmVarL (etaName x i) a, a) | (i, a) <- (enumerate as)]

-- Establishes naming convention for eta-expanding a constructor/global def.
etaName x i = "_" ++ x ++ show i

-- Returns the names of the args for a constructor
nameParams :: Var -> [Type] -> [Param]
nameParams x = zip (map (etaName x) [0..])

startName = "_start_"

-- Names used for de-/refunctionalization
applyName y = "_apply" ++ y ++ "_"
unfoldName y = "_unapply" ++ y ++ "_"
targetName = "_this_"
foldCtorName y i = "_fold" ++ y ++ "_" ++ show i ++ "_"
foldTypeName y = "_Fold" ++ y ++ "_"
unfoldTypeName y = "_Unfold" ++ y ++ "_"
unfoldCtorName y = "_unfold" ++ y ++ "_"
unfoldCtorArgName y i = "_unfold" ++ y ++ "_" ++ show i ++ "_"
unfoldCtorArgNames y n = [unfoldCtorArgName y i | i <- [0..n-1]]


-- Names used for affLin
affLinName x = '_' : x
tpUnitName = "_Unit_"
tmUnitName = "_unit_"
--tmNothingName i = "_nothing" ++ show i ++ "_"
--tmJustName i = "_just" ++ show i ++ "_"
--tpMaybeName i = "_Maybe" ++ show i ++ "_"

-- Constructors and case-ofs for affLin-generated datatypes
--tmNothing :: Int -> Term
--tmNothing i = TmVarG CtorVar (tmNothingName i) [] (tpMaybe i)

--tmJust :: Int -> Term -> Type -> Term
--tmJust i tm tp = TmVarG CtorVar (tmJustName i) [(tm, tp)] (tpMaybe i)

--tpMaybe i = TpVar (tpMaybeName i)

tmUnit = TmVarG CtorVar tmUnitName [] [] tpUnit
tpUnit = TpVar tpUnitName []

tpBoolName = "Bool"
tmTrueName = "True"
tmFalseName = "False"
tpBool = TpVar tpBoolName []
tmTrue = TmVarG CtorVar tmTrueName [] [] tpBool
tmFalse = TmVarG CtorVar tmFalseName [] [] tpBool

--tmElimMaybe :: Int -> Term -> Type -> Term -> (Var, Term) -> Type -> Term
--tmElimMaybe i tm tp ntm (jx, jtm) tp' =
--  TmCase tm (tpMaybeName i)
--    [Case (tmNothingName i) [] ntm,
--     Case (tmJustName i) [(jx, tp)] jtm] tp'

tmElimUnit :: Term -> Term -> Type -> Term
tmElimUnit utm tm tp = TmCase utm (tpUnitName, []) [Case tmUnitName [] tm] tp

unitCtors = [Ctor tmUnitName []]
--maybeCtors i tp = [Ctor (tmNothingName i) [], Ctor (tmJustName i) [tp]]

builtins :: [UsProg]
builtins = [
  UsProgData tpBoolName [] [Ctor tmFalseName [], Ctor tmTrueName []],
  UsProgData tpUnitName [] unitCtors
  ]

progBuiltins :: UsProgs -> UsProgs
progBuiltins (UsProgs ps end) =
  UsProgs (builtins ++ ps) end

instName :: Var -> Int -> Var
instName x i = x ++ "_inst" ++ show i
