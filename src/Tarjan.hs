-- Implementation of Tarjan's strongly connected components algorithm
-- Adapted from the pseudocode from
-- https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm

module Tarjan where
import qualified Data.Map as Map
import qualified Data.Set as Set

-- Keeps track of relevant information
data Tarjan a = Tarjan {
  indices :: Map.Map a Int,
  lowlinks :: Map.Map a Int,
  onStack :: Set.Set a,
  sStack :: [a],
  sccs :: [[a]]
}

defaultTarjan :: Ord a => Tarjan a
defaultTarjan = Tarjan {
  indices = mempty,
  lowlinks = mempty,
  onStack = mempty,
  sStack = [],
  sccs = []
}

-- Setter methods
modIndices :: Ord a => (Map.Map a Int -> Map.Map a Int) -> Tarjan a -> Tarjan a
modIndices f t = t { indices = f (indices t) }

modLowlinks :: Ord a => (Map.Map a Int -> Map.Map a Int) -> Tarjan a -> Tarjan a
modLowlinks f t = t { lowlinks = f (lowlinks t) }

modOnStack :: Ord a => (Set.Set a -> Set.Set a) -> Tarjan a -> Tarjan a
modOnStack f t = t { onStack = f (onStack t) }

modStack :: Ord a => ([a] -> [a]) -> Tarjan a -> Tarjan a
modStack f t = t { sStack = f (sStack t) }

modSccs :: Ord a => ([[a]] -> [[a]]) -> Tarjan a -> Tarjan a
modSccs f t = t { sccs = f (sccs t) }


-- Tarjan's algorithm implementation: goes from a graph to a
-- topologically-sorted array of strongly connected components
tarjan :: (Eq a, Ord a) => Map.Map a (Set.Set a) -> [[a]]
tarjan deps =
  sccs $
  foldr (\ v t -> if Map.member v (indices t) then t else strongconnect v t)
    defaultTarjan (Map.keys deps)
  where

    -- Adds a strongly connected component set with root v
    -- mkScc :: a -> Tarjan a -> Tarjan a
    mkScc v t =
      let h [] = []
          h (w : ws) = if w == v then [w] else (w : h ws)
          scc = h (sStack t) in
        modSccs ((:) scc) $
        modStack (drop (length scc)) $
        modOnStack (\ os -> Set.difference os (Set.fromList scc)) t
    
    -- strongconnect :: a -> Tarjan a -> Tarjan a
    strongconnect v t =
      let t' = modIndices (\ m -> Map.insert v (Map.size m) m) $
               modLowlinks (Map.insert v (Map.size (indices t))) $
               modStack ((:) v) $
               modOnStack (Set.insert v) t
          t'' = foldr
            (\ w t ->
               if Map.member w (indices t) then
                 (if not (Set.member w (onStack t)) then t else
                    modLowlinks (Map.insertWith min v (indices t Map.! w)) t)
               else
                 modLowlinks (\ lls -> Map.insertWith min v (lls Map.! w) lls)
                   (strongconnect w t))
            t' (deps Map.! v)
          t''' = if lowlinks t'' Map.! v == indices t'' Map.! v then mkScc v t'' else t''
      in
        t'''


{-main :: IO ()
main =
  let graph' = [("a", ["b"]),
                ("b", ["a", "b"]),
                ("c", ["a", "e", "d"]),
                ("d", ["e"]),
                ("e", ["c"])]
      graph = Map.fromList (fmap (\ (k, v) -> (k, Set.fromList v)) graph')
      sccs = tarjan graph
  in
    putStrLn (show sccs)
-}
