module Scope.Name where
import Struct.Lib

{- Naming conventions for internally-generated variables -}

delim = "/" -- should be unlexable

-- Used in various places for generating local variables
localName = TmV "x"

-- Used in monomorphization for instance of function or datatype x
instTmName :: TmName -> Int -> TmName
instTmName (TmN x) i = TmN (x ++ delim ++ "inst" ++ show i)
instTpName :: TpName -> Int -> TpName
instTpName (TpN x) i = TpN (x ++ delim ++ "inst" ++ show i)

-- Used in affine-to-linear transform for discarding recursive datatype y
-- global function
discardName y = TmN ("discard" ++ delim ++ show y)

-- Used for de-/refunctionalizing recursive datatype y
-- global functions
applyName (TpN y) = TmN ("unfold" ++ delim ++ y)
unapplyName (TpN y) = TmN ("fold" ++ delim ++ y)
-- datatypes and their constructors
defunTypeName (TpN y) = TpN ("Folded" ++ delim ++ y)
defunCtorName (TpN y) i = TmN ("folded" ++ delim ++ y ++ delim ++ "site" ++ show i)
refunTypeName (TpN y) = TpN ("Folded" ++ delim ++ y)
refunCtorName (TpN y) = TmN ("folded" ++ delim ++ y)

{- Although not defined here, here are some other internally-generated names:

_ is used as a placeholder in let <...> = ...

?0, ?1, ...: type variables
#0, #1, ...: tag variables

Any local variable x can become x0, x1, ....
Any type variable a can be a0, a1, ....  -}
