module Scope.Fresh (newVar, newVars) where
import Util.Helpers
import Struct.Lib
import qualified Data.Map as Map
import Data.Char

data SplitVar = SplitVar String Int String
succSplitVar (SplitVar pre i suf) = SplitVar pre (succ i) suf
instance Show SplitVar where
  show (SplitVar pre i suf) = pre ++ show i ++ suf

-- Splits abc14'' into SplitVar "abc" 14 "\'\'"
splitVar :: Var -> SplitVar
splitVar x =
  let (pre, i, suf) = h True (reverse x)
      pre' = reverse pre
      i' = reverse i
      suf' = reverse suf
      i'' = if null i' then 0 else succ (read i' :: Int)
  in
    SplitVar pre' i'' suf'
  where
    h :: Bool -> String -> (String, String, String)
    h b "" = ("", "", "")
    h True ('\'' : cs) =
      let (pre, i, suf) = h True cs in
        (pre, i, '\'' : suf)
    h True (c : cs) = h False (c : cs)
    h False (c : cs)
      | isDigit c =
        let (pre, i, suf) = h False cs in
          (pre, c : i, suf)
      | otherwise = (c : cs, "", "")

-- Given a map and a var, try new var names until it is no longer in the map
newVar :: Var -> Map Var a -> Var
newVar x g = if Map.member x g then h (splitVar x) else x
  where
    h x = let x' = show x in if Map.member x' g then h (succSplitVar x) else x'

newVars :: [Var] -> Map Var a -> [Var]
newVars xs g =
  fst (foldr (\ x (xs', g') -> let x' = newVar x g' in (x':xs', Map.insert x' () g')) ([], () <$ g) xs)
