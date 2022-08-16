{- Various helpful utility functions -}

module Util.Helpers where
import qualified Data.Map as Map
import qualified Data.Set as Set


-- It's annoying to have to write Map.Map k v
type Map k v = Map.Map k v
type Set v = Set.Set v

-- Returns the fst of a pair embedded in a functor type
-- For lists, this has type [(a, b)] -> [a]
fsts :: Functor f => f (a, b) -> f a
fsts = fmap fst

-- Returns the snd of a pair embedded in a functor type
-- For lists, this has type [(a, b)] -> [b]
snds :: Functor f => f (a, b) -> f b
snds = fmap snd

-- Maps on the left side of a sum (fmap does the right side already)
mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f (Left a) = Left (f a)
mapLeft f (Right c) = Right c

-- Creates a matrix of all possible combinations of two lists
kronecker :: [a] -> [b] -> [[(a, b)]]
kronecker as bs = [[(a, b) | b <- bs] | a <- as]

-- Calls a function for each possible combination of elements from two lists,
-- collecting into a list of results
kronwith :: (a -> b -> c) -> [a] -> [b] -> [c]
kronwith f as bs = [f a b | (a, b) <- concat (kronecker as bs)]

-- n-dimensional (rank?) Kronecker product
kronall :: [[a]] -> [[a]]
kronall = foldr (\ vs ws -> [(v : xs) | v <- vs, xs <- ws ]) [[]]

-- [a, b, c, ...] -> [(0, a), (1, b), (2, c), ...]
enumerate :: [a] -> [(Int, a)]
enumerate = zip [0..]

-- Argument-reordered version of maybe
maybe2 :: Maybe a -> b -> (a -> b) -> b
maybe2 m n j = maybe n j m

-- Uncurried <*>
infixl 4 <**>
(<**>) :: Applicative f => f (a -> b -> c) -> f (a, b) -> f c
(<**>) = (<*>) . fmap uncurry

-- Tries the first arg, if Nothing then returns the second arg
infixr 2 |?|
(|?|) :: Maybe a -> Maybe a -> Maybe a
Nothing |?| m_else = m_else
Just a |?| m_else = Just a

-- Nice little "return unit" function
okay :: Monad m => m ()
okay = return ()

-- Like foldl, but handles monad return types nicely
foldlM :: Monad m => (b -> a -> m b) -> m b -> [a] -> m b
foldlM f = foldl (\ mb a -> mb >>= \ b -> f b a)

-- Delimit a list of ShowS's with String
delimitWith :: String -> [ShowS] -> ShowS
delimitWith del [] = id
delimitWith del ss = foldr1 (\h t -> h . showString del . t) ss

parens :: String -> String
parens s = "(" ++ s ++ ")"

parensIf :: Bool -> String -> String
parensIf True = parens
parensIf False = id

-- zipWith enforcing length equal
pickyZipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
pickyZipWith f = go where
  go []     []     = []
  go (a:as) (b:bs) = f a b : go as bs
  go _      _      = error "pickyZipWith: list lengths don't match"

pickyZip :: [a] -> [b] -> [(a,b)]
pickyZip = pickyZipWith (,)

listDifference :: Ord a => [a] -> [a] -> [a]
listDifference as1 as2 = Set.toList (Set.difference (Set.fromList as1) (Set.fromList as2))
