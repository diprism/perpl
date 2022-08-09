module Util.SumProduct (sumProduct) where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (sortOn)
import Util.FGG
import Util.Tensor
import Util.Helpers
import Util.Graph

type MultiTensor = Map EdgeLabel (Tensor Weight)

multiTensorDistance :: MultiTensor -> MultiTensor -> Weight
multiTensorDistance mt1 mt2 =
  let diff = Map.differenceWith (\t1 t2 -> Just (tensorSub t1 t2)) mt1 mt2 in
    foldr max 0.0 (fmap (foldr max 0.0 . tensorFlatten) diff)

nonterminalGraph :: FGG -> Map EdgeLabel (Set EdgeLabel)
nonterminalGraph fgg = foldr (\ (Rule lhs rhs) g -> Map.insertWith Set.union lhs (nts rhs) g) (fmap (const mempty) (nonterminals fgg)) (repRules fgg)
  where nts rhs = Set.fromList [edge_label' e | e <- hgf_edges' rhs, edge_label' e `Map.member` nonterminals fgg]

sumProduct :: FGG -> Tensor Weight
sumProduct fgg =
  let
    -- Process the strongly-connected components that are reachable from start
    -- in topological order
    g = nonterminalGraph fgg
    nodes = reachable g (start fgg)
    sccs = filter (\c -> head c `elem` nodes) (scc g)
    z = foldr (sumProductSCC fgg) mempty (reverse sccs)
  in
    z Map.! (start fgg)

sumProductSCC :: FGG -> [EdgeLabel] -> MultiTensor -> MultiTensor
sumProductSCC fgg nts z = h (Map.union (zero fgg nts) z) where
  h prev =
    let cur = step fgg nts prev
        diff = multiTensorDistance cur prev
    in if diff < 1e-3 then cur else h cur

zero :: FGG -> [EdgeLabel] -> MultiTensor
zero fgg nts =
  Map.fromList [(x, zeros (nonterminalShape fgg x)) | x <- nts]

nonterminalShape :: FGG -> EdgeLabel -> [Int]
nonterminalShape fgg x = [length ((domains fgg) Map.! nl) | nl <- (nonterminals fgg) Map.! x]

repRules :: FGG -> [Rule NodeLabel]
repRules fgg = concat [ replicate c r | (c, r) <- rules fgg ]
  
step :: FGG -> [EdgeLabel] -> MultiTensor -> MultiTensor
step fgg nts z =
  Map.union (Map.fromList [ (x, stepNonterminal x) | x <- nts ]) z
  where

    stepNonterminal :: EdgeLabel -> Tensor Weight
    stepNonterminal x =
      foldr tensorAdd (zeros (nonterminalShape fgg x)) [stepRHS (castHGF rhs) | Rule lhs rhs <- repRules fgg, lhs == x]

    stepRHS :: HGF NodeLabel -> Tensor Weight
    stepRHS rhs = h [] nodes
      where
        -- Permute nodes so that the external nodes come first, in the
        -- order that they are listed in hgf_exts rhs
        perm = (hgf_exts rhs) ++ [i | i <- [0..length (hgf_nodes rhs)-1],
                                   not (i `elem` (hgf_exts rhs))]
        unperm = [i | (i, pi) <- sortOn (\(i, pi) -> pi) (enumerate perm)]
        nodes = fmap (hgf_nodes rhs !!) perm

        edge_wts = fmap (edgeWeights . edge_label) (hgf_edges rhs)

        -- h asst nodes is_ext
        -- asst is assignment to processed nodes, *reversed*
        -- nodes is remaining nodes
        h asst (node:nodes) =
          let
            Node _ d = node
            size = length (domains fgg Map.! d)
            sub = [h (i:asst) nodes | i <- [0..size-1]]
          in
            if length asst < length (hgf_exts rhs) then
              Vector sub -- external: don't contract
            else
              foldr tensorAdd (Scalar 0.0) sub -- internal: contract

        h asst [] =
          let
            asst_rev = reverse asst
            asst_unperm = fmap (asst_rev !!) unperm
            edge_assts = [(fmap (asst_unperm !!) (edge_atts e)) | e <- hgf_edges rhs]
          in
            foldr tensorTimes (Scalar 1.0) [w !!! (fmap SliceIndex asst) | (w, asst) <- zip edge_wts edge_assts]

    edgeWeights :: EdgeLabel -> Tensor Weight
    edgeWeights el =
      case Map.lookup el z of
                Just w -> w
                Nothing -> case Map.lookup el (factors fgg) of
                             Just (_, Just w) -> w
                             _ -> error (show el ++ " not found (extern not supported yet)")
            
