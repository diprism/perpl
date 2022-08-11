module Scope.Name where
import Data.List (intercalate)
import Struct.Lib

{- Naming conventions for internally-generated variables -}

-- Naming convention for testing equality two terms of the same type
typeFactorName tp = "==" ++ show tp

eqFactorName tp n = "[" ++ show n ++ "]" ++ "==" ++ show tp

-- Naming convention for factor v=(v1,v2)
pairFactorName tp1 tp2 = "v=(" ++ show (TpArr tp1 tp2) ++ ")"

ampFactorName :: [Type] -> Int -> String
ampFactorName tps i = "v=<" ++ intercalate ", " [show tp | tp <- tps] ++ ">." ++ show i

prodFactorName :: [Type] -> String
prodFactorName tps = "v=(" ++ intercalate ", " (map show tps) ++ ")" 

prodValName :: [String] -> String
prodValName tms = "(" ++ intercalate ", " tms ++ ")"

ctorFactorName :: Var -> [Type] -> Type -> String
ctorFactorName x as tp = "v=" ++ show (TmVarG CtorVar x [] [] (paramsToArgs (nameParams x as)) tp)

-- Establishes naming convention for eta-expanding a constructor/global def.
etaName :: Var -> Int -> Var
etaName (Var x) i = Var ("_" ++ x ++ show i)

-- Returns the names of the args for a constructor
nameParams :: Var -> [Type] -> [Param]
nameParams x = zip (map (etaName x) [0..])

startName = "_start_"

-- Names used for de-/refunctionalization
applyName (Var y) = Var ("_apply" ++ y ++ "_")
unfoldName (Var y) = Var ("_unapply" ++ y ++ "_")
targetName = Var "_this_"
targetName2 = Var "_this_'"
foldCtorName (Var y) i = Var ("_fold" ++ y ++ "_" ++ show i ++ "_")
foldTypeName (Var y) = Var ("_Fold" ++ y ++ "_")
unfoldTypeName (Var y) = Var ("_Unfold" ++ y ++ "_")
unfoldCtorName (Var y) = Var ("_unfold" ++ y ++ "_")
unfoldCtorArgName (Var y) i = Var ("_unfold" ++ y ++ "_" ++ show i ++ "_")
unfoldCtorArgNames y n = [unfoldCtorArgName y i | i <- [0..n-1]]


-- Names used for affLin
discardName y = Var ("_discard" ++ show y ++ "_")

-- Names used for monomorphization
instName :: Var -> Int -> Var
instName (Var x) i = Var (x ++ "_inst" ++ show i)
