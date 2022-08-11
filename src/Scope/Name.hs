module Scope.Name where
import Struct.Lib

{- Naming conventions for internally-generated variables -}

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
discardName y = "_discard" ++ y ++ "_"

-- Names used for monomorphization
instName :: Var -> Int -> Var
instName x i = x ++ "_inst" ++ show i
