module Scope.Fresh (newVar, newVars) where
import Util.Helpers
import qualified Data.Set as Set
import Data.Char (isDigit)
import Data.String (IsString(fromString))
import Data.List (mapAccumL)

data SplitVar = SplitVar String Int String

rejoin :: IsString var => SplitVar -> var
rejoin (SplitVar pre i suf) = fromString (pre ++ show i ++ suf)

-- Splits abc14'' into SplitVar "abc" 14 "\'\'"
splitVar :: String -> SplitVar
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

-- Given a predicate, set, and var,
-- try new var names until it no longer satisfies the predicate or appears in the set
newVar' :: (Ord var, Show var, IsString var) => (var -> Bool) -> Set var -> var -> (Set var, var)
newVar' used g x = (Set.insert y g, y)
  where SplitVar pre i suf = splitVar (show x)
        y:_ = filter (\y -> not (used y || Set.member y g))
                     (x : [ fromString (rejoin (SplitVar pre j suf)) | j <- [i..] ])

newVar :: (Ord var, Show var, IsString var) => var -> (var -> Bool) -> var
newVar x used = snd (newVar' used Set.empty x)

newVars :: (Ord var, Show var, IsString var) => [var] -> (var -> Bool) -> [var]
newVars xs used = snd (mapAccumL (newVar' used) Set.empty xs)
