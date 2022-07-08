module Util.SumProduct (sumProduct) where
import qualified Data.Map as Map
import Data.List (sortOn)
import Util.FGG
import Util.Tensor
import Util.Helpers

type MultiTensor = Map String (Tensor Prob)

multiTensorDistance :: MultiTensor -> MultiTensor -> Prob
multiTensorDistance mt1 mt2 =
  let diff = Map.differenceWith (\t1 t2 -> Just (tensorSub t1 t2)) mt1 mt2 in
    foldr max 0.0 (fmap (foldr max 0.0 . tensorFlatten) diff)

sumProduct :: FGG Domain -> Tensor Prob
sumProduct fgg = h (zero fgg) where
  h prev =
    let cur = step fgg prev
        diff = multiTensorDistance cur prev
    in if diff < 1e-3 then cur Map.! (start fgg) else h cur

zero :: FGG Domain -> MultiTensor
zero fgg =
  Map.fromList [(x, zeros (nonterminalShape fgg x)) | x <- Map.keys (nonterminals fgg)]

nonterminalShape :: FGG Domain -> String -> [Int]
nonterminalShape fgg x = [length ((domains fgg) Map.! nl) | nl <- (nonterminals fgg) Map.! x]

repRules :: FGG d -> [Rule Label]
repRules fgg = concat [ replicate c r | (c, r) <- rules fgg ]
  
step :: FGG Domain -> MultiTensor -> MultiTensor
step fgg z =
  Map.fromList [ (x, stepNonterminal x) | x <- Map.keys (nonterminals fgg) ]
  where

    stepNonterminal :: String -> Tensor Prob
    stepNonterminal x =
      foldr tensorAdd (zeros (nonterminalShape fgg x)) [stepRHS rhs | Rule lhs rhs <- repRules fgg, lhs == x]

    stepRHS :: HGF Label -> Tensor Prob
    stepRHS rhs = h [] nodes
      where
        -- Permute nodes so that the external nodes come first, in the
        -- order that they are listed in hgf_exts rhs
        perm = (hgf_exts rhs) ++ [i | i <- [0..length (hgf_nodes rhs)-1],
                                   not (i `elem` (hgf_exts rhs))]
        unperm = [i | (i, pi) <- sortOn (\(i, pi) -> pi) (enumerate perm)]
        nodes = fmap (hgf_nodes rhs !!) perm

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
          in
            Scalar (foldr (*) 1.0 [edgeWeight (edge_label e) (fmap (asst_unperm !!) (edge_atts e)) | e <- hgf_edges rhs])
            
    -- weight of edge with label el under assignment asst to edge's attachment nodes
    edgeWeight :: String -> [Int] -> Prob
    edgeWeight el asst =
      let w = case Map.lookup el z of
                Just w -> w
                Nothing -> case Map.lookup el (factors fgg) of
                             Just (_, Just w) -> w
                             _ -> error (show el ++ " not found (extern not supported yet)")
          Scalar w_asst = w !!! (fmap SliceIndex asst)
      in
        w_asst
