module Util.SumProduct (sumProduct, prettySumProduct) where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (sortOn, intercalate)
import Util.FGG
import Util.Tensor
import Util.Helpers
import Util.Graph

type MultiTensor = Map EdgeLabel (Tensor Weight)

multiTensorDistance :: MultiTensor -> MultiTensor -> Weight
multiTensorDistance mt1 mt2 =
  let diff = Map.differenceWith (\t1 t2 -> Just (tensorSub t1 t2)) mt1 mt2 in
    foldr max 0.0 (fmap (foldr max 0.0 . tensorFlatten) diff)

nonterminalGraph :: FGG tensor -> Map EdgeLabel (Set EdgeLabel)
nonterminalGraph fgg = foldr (\ (Rule lhs rhs) g -> Map.insertWith Set.union lhs (nts rhs) g) (fmap (const mempty) (nonterminals fgg)) (rules fgg)
  where nts rhs = Set.fromList [edge_label e | e <- hgf_edges rhs, edge_label e `Map.member` nonterminals fgg]

sumProduct :: FGG Tensor -> Tensor Weight
sumProduct fgg =
  let
    -- Process the strongly-connected components that are reachable from start
    -- in topological order
    g = nonterminalGraph fgg
    nodes = reachable g (start fgg)
    sccs = filter f (scc g) where
      f (TrivialSCC v) = v `elem` nodes
      f (NontrivialSCC vs) = head vs `elem` nodes
    z = foldr (sumProductSCC fgg) mempty (reverse sccs)
  in
    z Map.! (start fgg)

sumProductSCC :: FGG Tensor -> SCC EdgeLabel -> MultiTensor -> MultiTensor
sumProductSCC fgg (NontrivialSCC nts) z = h (Map.union (zero fgg nts) z) where
  h prev =
    let cur = step fgg nts prev
        diff = multiTensorDistance cur prev
    in if diff < 1e-3 then cur else h cur
sumProductSCC fgg (TrivialSCC nt) z = step fgg [nt] (Map.union (zero fgg [nt]) z)

tensorToAssoc :: FGG Tensor -> EdgeLabel -> Tensor a -> [([Value], a)]
tensorToAssoc fgg el = h (nonterminals fgg Map.! el) where
  h [] (Scalar w) =
      [([], w)]
  h (nl:nls) (Vector ts) =
    let vals = (domains fgg) Map.! nl
        maps = [h nls t | t <- ts]
    in
      [(v:vs, w) | (v, m) <- zip vals maps, (vs, w) <- m]
  h _ _ =
    error "nonterminal label and weight tensor have different shapes"

prettySumProduct fgg =
  intercalate "\n" [intercalate " " [s | Value s <- vals] ++ "\t" ++ show w | (vals, w) <- (tensorToAssoc fgg (start fgg) (sumProduct fgg))]

zero :: FGG Tensor -> [EdgeLabel] -> MultiTensor
zero fgg nts =
  Map.fromList [(x, zeros (nonterminalShape fgg x)) | x <- nts]

nonterminalShape :: FGG Tensor -> EdgeLabel -> [Int]
nonterminalShape fgg x = [length ((domains fgg) Map.! nl) | nl <- (nonterminals fgg) Map.! x]

step :: FGG Tensor -> [EdgeLabel] -> MultiTensor -> MultiTensor
step fgg nts z =
  Map.union (Map.fromList [ (x, stepNonterminal x) | x <- nts ]) z
  where

    stepNonterminal :: EdgeLabel -> Tensor Weight
    stepNonterminal x =
      foldr tensorAdd (zeros (nonterminalShape fgg x)) [stepRHS rhs | Rule lhs rhs <- rules fgg, lhs == x]

    stepRHS :: HGF -> Tensor Weight
    stepRHS (HGF nodes edges exts) = h [] nodes'
      where
        -- Number the nodes of the RHS
        m = Map.fromList (zip (fsts nodes) [0..])
        edges' = [[m Map.! n | (n, d) <- atts] | Edge atts el <- edges]
        exts' = [m Map.! n | (n, d) <- exts]
        
        -- Permute nodes so that the external nodes come first, in the
        -- order that they are listed in rhs
        perm = exts' ++ [i | i <- [0..length nodes-1], not (i `elem` exts')]
        unperm = [i | (i, pi) <- sortOn (\(i, pi) -> pi) (enumerate perm)]
        nodes' = fmap (nodes !!) perm

        edge_wts = [edgeWeights el | Edge atts el <- edges]

        -- h asst nodes
        -- asst is assignment to processed nodes, *reversed*
        -- nodes is remaining nodes
        h asst ((_, d):nodes) =
          let
            size = length (domains fgg Map.! d)
            sub = [h (i:asst) nodes | i <- [0..size-1]]
          in
            if length asst < length exts' then
              Vector sub -- external: don't contract
            else
              foldr tensorAdd (Scalar 0.0) sub -- internal: contract

        h asst [] =
          let
            asst_rev = reverse asst
            asst_unperm = fmap (asst_rev !!) unperm
            edge_assts = fmap (fmap (asst_unperm !!)) edges'
          in
            foldr tensorTimes (Scalar 1.0) [w !!! (fmap SliceIndex asst) | (w, asst) <- zip edge_wts edge_assts]

    edgeWeights :: EdgeLabel -> Tensor Weight
    edgeWeights el =
      case Map.lookup el z of
                Just w -> w
                Nothing -> case Map.lookup el (factors fgg) of
                             Just (_, w) -> w
                             Nothing -> error ("couldn't find weights for " ++ show el)
