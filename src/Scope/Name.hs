module Scope.Name where
import Struct.Lib

{- Naming conventions for internally-generated variables -}

-- Used in various places for generating local variables
etaName :: Var -> Int -> Var
etaName (Var x) i = Var ("_" ++ x ++ show i)
localName = Var "x"

-- Used in monomorphization for instance of function or datatype x
instName :: Var -> Int -> Var
instName (Var x) i = Var (x ++ "_inst" ++ show i)

-- Used in affine-to-linear transform for discarding recursive datatype y
-- global function
discardName y = Var ("_discard" ++ show y ++ "_")

-- Used for de-/refunctionalizing recursive datatype y
-- global functions
applyName (Var y) = Var ("_apply" ++ y ++ "_")
unfoldName (Var y) = Var ("_unapply" ++ y ++ "_")
-- datatypes and their constructors
foldCtorName (Var y) i = Var ("_fold" ++ y ++ "_" ++ show i ++ "_")
foldTypeName (Var y) = Var ("_Fold" ++ y ++ "_")
unfoldTypeName (Var y) = Var ("_Unfold" ++ y ++ "_")
unfoldCtorName (Var y) = Var ("_unfold" ++ y ++ "_")

{- Although not defined here, here are some other internally-generated names:

_ is used as a placeholder in let <...> = ...

?0, ?1, ...: type variables
#0, #1, ...: tag variables

Any local variable x can become x0, x1, ....
Any type variable a can be a0, a1, ....  -}
