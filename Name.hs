module Name where
import Exprs
import Util
import Show

-- Naming convention for testing equality two terms of the same type
typeFactorName :: Type -> String
typeFactorName tp = "==" ++ show tp

-- Naming convention for factor v=(v1,v2)
pairFactorName :: Type -> Type -> String
pairFactorName tp1 tp2 = "v=(" ++ show (TpArr tp1 tp2) ++ ")"

internalFactorName :: Term -> String
internalFactorName tm = "v=" ++ show tm

-- Naming convention for constructor factor
ctorFactorName :: Var -> [(Term, Type)] -> Type -> String
ctorFactorName x as tp = internalFactorName (TmVarG DefVar x as tp)

ctorFactorNameDefault :: Var -> [Type] -> Type -> String
ctorFactorNameDefault x as = ctorFactorName x (map (\ (i, a) -> (TmVarL (etaName x i) a, a)) (enumerate as))

-- Establishes naming convention for eta-expanding a constructor.
-- So Cons h t -> (\ ?Cons0. \ ?Cons1. Cons ?Cons0 ?Cons1) h t.
-- This is necessary so that the FGG can use one rule for each
-- constructor, and not for each usage of it in the code.
-- It also fixes the issue of partially-applied constructors.
etaName :: Var -> Int -> Var
etaName x i = "?" ++ x ++ show i

aff2linName :: Var -> Var
aff2linName x = '%' : x

-- Returns the names of the args for a constructor
getArgs :: Var -> [Type] -> [(Var, Type)]
getArgs x tps =
  zip (map (etaName x) [0..length tps - 1]) tps

ctorDefault :: Var -> [Type] -> Type -> Term
ctorDefault x as y = TmVarG CtorVar x (map (\ (a, atp) -> (TmVarL a atp, atp)) (getArgs x as)) y

applyName :: Int -> Var
applyName i = "%apply%" ++ show i

applyTargetName :: Int -> Var
applyTargetName i = "%unfold%" ++ show i
