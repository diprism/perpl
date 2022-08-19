module Scope.Name where
import Struct.Lib

{- Naming conventions for internally-generated variables -}

delim = "/" -- should be unlexable

-- Used in various places for generating local variables
localName = Var "x"

-- Used in monomorphization for instance of function or datatype x
instName :: Var -> Int -> Var
instName (Var x) i = Var (x ++ delim ++ "inst" ++ show i)

-- Used in affine-to-linear transform for discarding recursive datatype y
-- global function
discardName y = Var ("discard" ++ delim ++ show y)

-- Used for de-/refunctionalizing recursive datatype y
-- global functions
applyName (Var y) = Var ("unfold" ++ delim ++ y)
unapplyName (Var y) = Var ("fold" ++ delim ++ y)
-- datatypes and their constructors
defunTypeName (Var y) = Var ("Folded" ++ delim ++ y)
defunCtorName (Var y) i = Var ("folded" ++ delim ++ y ++ delim ++ "site" ++ show i)
refunTypeName (Var y) = Var ("Folded" ++ delim ++ y)
refunCtorName (Var y) = Var ("folded" ++ delim ++ y)

{- Although not defined here, here are some other internally-generated names:

_ is used as a placeholder in let <...> = ...

?0, ?1, ...: type variables
#0, #1, ...: tag variables

Any local variable x can become x0, x1, ....
Any type variable a can be a0, a1, ....  -}
