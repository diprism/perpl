module RuleM where
import Data.List
import qualified Data.Map as Map
import Exprs
import FGG
import Util
import Name

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

addFactor :: Var -> PreWeight -> RuleM
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

isRule :: String -> RuleM -> Bool
isRule lhs (RuleM rs xs nts fs) = any (\ (Rule lhs' _) -> lhs == lhs') rs


getPairWeights :: Type -> Type -> PreWeight
getPairWeights tp1 tp2 = PairWeight (show tp1, show tp2)


splitCtorsAt :: [Ctor] -> Var -> ([Ctor], [Ctor])
splitCtorsAt [] x = ([], [])
splitCtorsAt (Ctor x' as : cs) x
  | x == x' = ([], cs)
  | otherwise =
    let (b, a) = splitCtorsAt cs x in
      (Ctor x' as : b, a)

invWeightsData :: WeightsH a -> a
invWeightsData (WeightsData ws) = ws
invWeightsData (WeightsDims ws) = error "In invWeightsData, expected WeightsData"

invWeightsDims :: WeightsH a -> WeightsH [a]
invWeightsDims (WeightsDims ws) = ws
invWeightsDims (WeightsData ws) = error "In invWeightsDims, expected WeightsDims"

weightsPush :: WeightsH [a] -> [WeightsH a]
weightsPush (WeightsData ws) = map WeightsData ws
weightsPush (WeightsDims ws) = map WeightsDims (weightsPush ws)

weightsPull :: [WeightsH a] -> WeightsH [a]
--weightsPull [] = ???
weightsPull (WeightsData ws : ws') =
  WeightsData (map invWeightsData (WeightsData ws : ws'))
weightsPull (WeightsDims ws : ws') =
  let ws'' = map invWeightsDims (WeightsDims ws : ws') in
  WeightsDims $ weightsPull ws''

getExternWeights :: (Type -> [String]) -> [Type] -> Type -> PreWeight
getExternWeights dom ps tp =
  let rep = \ tp a -> WeightsDims (weightsPull (replicate (length (dom tp)) a))
      iws = rep tp (WeightsData 0) in
    ThisWeight $ foldr rep iws ps

getCtorWeightsAll :: (Type -> [String]) -> [Ctor] -> Type -> [(String, PreWeight)]
getCtorWeightsAll dom cs y =
  concat $ flip map cs $ \ (Ctor x as) ->
    flip map (getCtorWeights dom (Ctor x as) cs) $ \ (as', ws) ->
      let as'' = map (\ (x, atp) -> (TmVarL x atp, atp)) (zip as' as) in
        (ctorFactorName x as'' y, ws)

getCtorWeights :: (Type -> [String]) -> Ctor -> [Ctor] -> [([String], PreWeight)]
getCtorWeights dom (Ctor x as) cs =
  let (cs_before, cs_after) = splitCtorsAt cs x
      csf = \ cs' -> sum (map (\ (Ctor x' as') -> product (map (length . dom) as')) cs')
      cs_b' = csf cs_before
      cs_a' = csf cs_after
      mkrow = \ mask -> replicate cs_b' 0 ++ mask ++ replicate cs_a' 0
  in
    flip map (kronpos (map dom as)) $ \ as' -> (,) (map (\ (_, _, a) -> a) as') $ ThisWeight $
      let (out, pos) = foldr (\ (i, o, _) (l, j) -> (l * o, l * i + j)) (1, 0) as'
          row = WeightsDims $ WeightsData $ mkrow (weightsRow pos out) in
      foldr (\ (i, o, a) ws -> WeightsDims $ weightsPull [if i == j then ws else fmap (\ _ -> 0) ws | j <- [0..o - 1]]) row as'

getCtorWeightsFlat :: (Type -> [String]) -> Ctor -> [Ctor] -> PreWeight
getCtorWeightsFlat dom (Ctor x as) cs =
  let (cs_before, cs_after) = splitCtorsAt cs x
      csf = \ cs' -> sum (map (\ (Ctor x' as') -> product (map (length . dom) as')) cs')
      cs_b' = csf cs_before
      cs_a' = csf cs_after
      mkrow = \ mask -> replicate cs_b' 0 ++ mask ++ replicate cs_a' 0
  in
    ThisWeight $
      foldr
        (\ avs jl2ws j l -> WeightsDims $ weightsPull [jl2ws (l * i + j) (l * length avs) | i <- [0..length avs - 1]])
        (\ j l -> WeightsDims (WeightsData (mkrow (weightsRow j l))))
        (map dom as) 0 1

-- Identity matrix
getCtorEqWeights :: Int {- num of possible values -} -> PreWeight
getCtorEqWeights cs =
  let is = [0..cs - 1] in
    ThisWeight $ fmap (\ (i, j) -> if i == j then 1 else 0) $
      matrixWeight $ kronecker is is


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

