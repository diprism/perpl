module Free where
import Exprs
import qualified Data.Map as Map

freeVars :: Term -> Map.Map Var Int
freeVars (TmVar x) = Map.singleton x 1
freeVars (TmLam x tp tm tp') = Map.delete x $ freeVars tm
freeVars (TmApp tm tm') = Map.unionWith (+) (freeVars tm) (freeVars tm')
freeVars (TmCase tm cs) = foldr (Map.unionWith max . freeVarsCase) (freeVars tm) cs
freeVars (TmSamp d y) = Map.empty -- TODO: should this return a list of y's ctors?

freeVarsCase :: Case -> Map.Map Var Int
freeVarsCase (Case c xs tm) = foldr Map.delete (freeVars tm) xs

freeOccurrences :: Var -> Term -> Int
freeOccurrences x tm = findWithDefault 0 x (freeVars tm)

isFree :: Var -> Term -> Bool
isFree x tm = member x (freeVars tm)

isAff :: Var -> Term -> Bool
isAff x tm = freeOccurrences x tm <= 1

isLin :: Var -> Term -> Bool
isLin x tm = freeOccurrences x tm == 1
