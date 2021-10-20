module RuleM where
import Data.List
import qualified Data.Map as Map
import Exprs
import FGG
import Util
import Name
import Tensor

-- RuleM monad-like datatype and funcions
type External = (Var, Type)
data RuleM = RuleM [Rule] [External] [Nonterminal] [Factor]

-- RuleM instances of >>= and >= (since not
-- technically a monad, need to pick new names)
infixl 1 +>=, +>, +*>=
(+>=) :: RuleM -> ([External] -> RuleM) -> RuleM
RuleM rs xs nts fs +>= g =
  let RuleM rs' xs' nts' fs' = g xs in
    RuleM (rs ++ rs')
          (unionBy (\ (a, _) (a', _) -> a == a') xs xs')
          (nts ++ nts')
          (concatFactors fs fs')

(+>) :: RuleM -> RuleM -> RuleM
r1 +> r2 = r1 +>= \ _ -> r2

-- Sequence together RuleMs, collecting each's externals
(+*>=) :: [RuleM] -> ([[External]] -> RuleM) -> RuleM
rs +*>= rf =
  let (r, xss) = foldr (\ r' (r, xss) -> let RuleM rs' xs' nts' fs' = r' in (r +> r', xs' : xss)) (returnRule, []) rs in
    r +> rf xss

-- Add a list of external nodes
addExts :: [External] -> RuleM
addExts xs = RuleM [] xs [] []

-- Add a single external node
addExt :: Var -> Type -> RuleM
addExt x tp = addExts [(x, tp)]

addNonterms :: [Nonterminal] -> RuleM
addNonterms nts = RuleM [] [] nts []

-- Add a single nonterminal
addNonterm :: Var -> Type -> RuleM
addNonterm x tp = addNonterms [(x, tp)]

-- Add a list of rules
addRules :: [Rule] -> RuleM
addRules rs = RuleM rs [] [] []

-- Add a single rule
addRule :: Rule -> RuleM
addRule r = addRules [r]

-- Add a rule from the given components
addRule' :: Term -> [Type] -> [Edge] -> [Int] -> RuleM
addRule' lhs ns es xs = addRule $ Rule (show lhs) $ HGF ns es xs

addFactor :: Var -> Weights -> RuleM
addFactor x w = RuleM [] [] [] [(x, w)]

-- Do nothing new
returnRule :: RuleM
returnRule = RuleM [] [] [] []

-- Extract rules from a RuleM
getRules :: RuleM -> [Rule]
getRules (RuleM rs xs nts fs) = rs

-- Removes all external nodes from a RuleM
resetExts :: RuleM -> RuleM
resetExts (RuleM rs xs nts fs) = RuleM rs [] nts fs

-- Overrides the external nodes from a RuleM
setExts :: [External] -> RuleM -> RuleM
setExts xs (RuleM rs _ nts fs) = RuleM rs xs nts fs

-- Returns if this lhs is already used
isRule :: String -> RuleM -> Bool
isRule lhs (RuleM rs xs nts fs) = any (\ (Rule lhs' _) -> lhs == lhs') rs

-- Returns the Weights for a function tp1 -> tp2
getPairWeights :: Int -> Int -> Weights
getPairWeights tp1s tp2s = tensorToWeights (tensorId [tp1s, tp2s])

-- Returns the ctors to the left and to the right of one named x
-- (but discards the ctor named x itself)
splitCtorsAt :: [Ctor] -> Var -> ([Ctor], [Ctor])
splitCtorsAt [] x = ([], [])
splitCtorsAt (Ctor x' as : cs) x
  | x == x' = ([], cs)
  | otherwise =
    let (b, a) = splitCtorsAt cs x in
      (Ctor x' as : b, a)

-- Computes the weights for a function with params ps and return type tp
getExternWeights :: (Type -> [String]) -> [Type] -> Type -> Weights
getExternWeights dom ps tp =
  let rep = \ tp a -> WeightsDims (weightsPull (replicate (length (dom tp)) a))
      iws = rep tp (WeightsData 0) in
    foldr rep iws ps

-- Computes the weights for a list of constructors
getCtorWeightsAll :: (Type -> [String]) -> [Ctor] -> Type -> [(String, Weights)]
getCtorWeightsAll dom cs y =
  concat $ flip map cs $ \ (Ctor x as) ->
    flip map (getCtorWeights dom (Ctor x as) cs) $ \ (as', ws) ->
      let as'' = map (\ (x, atp) -> (TmVarL x atp, atp)) (zip as' as) in
        (ctorFactorName x as'' y, ws)

-- Computes the weights for a specific constructor
getCtorWeights :: (Type -> [String]) -> Ctor -> [Ctor] -> [([String], Weights)]
getCtorWeights dom (Ctor x as) cs =
  let (cs_before, cs_after) = splitCtorsAt cs x
      csf = \ cs' -> sum (map (\ (Ctor x' as') -> product (map (length . dom) as')) cs')
      cs_b' = csf cs_before
      cs_a' = csf cs_after
      mkrow = \ mask -> replicate cs_b' 0 ++ mask ++ replicate cs_a' 0
  in
    flip map (kronpos (map dom as)) $ \ as' -> (,) (map (\ (_, _, a) -> a) as') $
      let (out, pos) = foldr (\ (i, o, _) (l, j) -> (l * o, l * i + j)) (1, 0) as'
          row = WeightsDims $ WeightsData $ mkrow (weightsRow pos out) in
      foldr (\ (i, o, a) ws -> WeightsDims $ weightsPull [if i == j then ws else fmap (\ _ -> 0) ws | j <- [0..o - 1]]) row as'

-- Computes the weights for a specific constructor (can't remember how this is different from getCtorWeights above :P)
getCtorWeightsFlat :: (Type -> [String]) -> Ctor -> [Ctor] -> Weights
getCtorWeightsFlat dom (Ctor x as) cs =
  let (cs_before, cs_after) = splitCtorsAt cs x
      csf = \ cs' -> sum (map (\ (Ctor x' as') -> product (map (length . dom) as')) cs')
      cs_b' = csf cs_before
      cs_a' = csf cs_after
      mkrow = \ mask -> replicate cs_b' 0 ++ mask ++ replicate cs_a' 0
  in
    foldr
      (\ avs jl2ws j l -> WeightsDims $ weightsPull [jl2ws (l * i + j) (l * length avs) | i <- [0..length avs - 1]])
      (\ j l -> WeightsDims (WeightsData (mkrow (weightsRow j l))))
      (map dom as) 0 1

-- Identity matrix
getCtorEqWeights :: Int {- num of possible values -} -> Weights
getCtorEqWeights cs =
  let is = [0..cs - 1] in
    fmap (\ (i, j) -> if i == j then 1 else 0) $
      matrixWeight $ kronecker is is

getAmpWeights :: (Type -> [String]) -> [Type] -> [Weights]
getAmpWeights dom tps =
  let tpvs = map dom tps in
    map (\ (i, itpvs) ->
           WeightsDims $ WeightsDims $ WeightsData
             (concatMap
               (\ (j, vs) ->
                   [[if l == k && i == j then 1 else 0 | (l, _) <- enumerate itpvs] | (k, _) <- enumerate vs])
               (enumerate tpvs))) (enumerate tpvs)

getProdWeights :: [[String]] -> [([String], Weights)]
getProdWeights tpvs =
  let vss = kronpos tpvs in
  flip map vss $ \ as' -> (,) (map (\ (_, _, a) -> a) as') $ 
    let (out, pos) = foldr (\ (i, o, _) (l, j) -> (l * o, l * i + j)) (1, 0) as' in
      foldr (\ (i, o, a) ws -> WeightsDims (weightsPull [if i == j then ws else fmap (\ _ -> 0) ws | j <- [0..o - 1]])) (WeightsDims (WeightsData (weightsRow pos out))) as'

getProdWeightsV :: [[String]] -> Weights
getProdWeightsV tpvs =
  let vss = kronpos tpvs
      dims = [length vs | vs <- tpvs] in
    tensorToWeights (tensorId dims)

shapeH :: (a -> [Int]) -> WeightsH a -> [Int]
shapeH f (WeightsData a) = f a
shapeH f (WeightsDims as) = shapeH (\ bs -> length bs : f (bs !! 0)) as
shape :: Weights -> [Int]
shape = shapeH (\ _ -> [])


-- Given a set of external nodes, this returns a pair where the first
-- is basically just the nub of the concatenated nodes, and the second
-- is a mapping from each node's original position to its new one in
-- the first part.
-- It takes a list of lists to allow you to more easily keep track of
-- where an arbitrary number of externals went.
combineExts :: Ord a => [[(a, x)]] -> ([(a, x)], [[Int]])
combineExts = h Map.empty 0 where

  index :: Ord a => Map.Map a Int -> Int -> [(a, x)] -> (Map.Map a Int, [(a, x)])
  index ixs i [] = (ixs, [])
  index ixs i (a : as) = case Map.lookup (fst a) ixs of
    Nothing -> fmap ((:) a) (index (Map.insert (fst a) i ixs) (succ i) as)
    Just ia -> index ixs i as
  
  h :: Ord a => Map.Map a Int -> Int -> [[(a, x)]] -> ([(a, x)], [[Int]])
  h ixs i [] = ([], [])
  h ixs i (as : rest) =
    let (ixs', as') = index ixs i as
        is = map (\ (a, _) -> ixs' Map.! a) as
        (rs, ms) = h ixs' (i + length as') rest in
      (as' ++ rs, is : ms)

