module RuleM where
import Data.List
import Exprs
import FGG
import Util

-- RuleM monad-like datatype and funcions
type External = (Var, Type)
data RuleM = RuleM [Rule] [External] [Factor]

-- RuleM instances of >>= and >= (since not
-- technically a monad, need to pick new names)
infixl 1 +>=, +>, +*>=
(+>=) :: RuleM -> ([External] -> RuleM) -> RuleM
RuleM rs xs fs +>= g =
  let RuleM rs' xs' fs' = g xs in
    RuleM (rs ++ rs') (xs ++ xs') (concatFactors fs fs')

(+>) :: RuleM -> RuleM -> RuleM
r1 +> r2 = r1 +>= \ _ -> r2

(+*>=) :: [RuleM] -> ([[External]] -> RuleM) -> RuleM
rs +*>= rf =
  let (r, xss) = foldr (\ r' (r, xss) -> let RuleM rs' xs' fs' = r' in (r +> r', xs' : xss)) (returnRule, []) rs in
    r +> rf xss

-- Add a list of external nodes
addExts :: [(Var, Type)] -> RuleM
addExts xs = RuleM [] xs []

-- Add a single external node
addExt :: Var -> Type -> RuleM
addExt x tp = addExts [(x, tp)]

-- Add a list of rules
addRules :: [Rule] -> RuleM
addRules rs = RuleM rs [] []

-- Add a single rule
addRule :: Rule -> RuleM
addRule r = addRules [r]

-- Add a rule from the given components
addRule' :: Term -> [Type] -> [Edge] -> [Int] -> RuleM
addRule' lhs ns es xs = addRule $ Rule (show lhs) $ HGF ns es xs

addFactor :: Var -> PreWeight -> RuleM
addFactor x w = RuleM [] [] [(x, w)]

-- Do nothing new
returnRule :: RuleM
returnRule = RuleM [] [] []

-- Extract rules from a RuleM
getRules :: RuleM -> [Rule]
getRules (RuleM rs xs fs) = rs



getPairWeights :: Type -> Type -> PreWeight
getPairWeights tp1 tp2 = PairWeight ((show tp1), (show tp2))

getCtorWeights :: Int {- ctor index -} -> Int {- num of ctors -} -> PreWeight
getCtorWeights ci cs = ThisWeight $ WeightsDims $ WeightsData $ weightsRow ci cs

-- Identity matrix
getCtorEqWeights :: Int {- num of ctors -} -> PreWeight
getCtorEqWeights cs =
  let is = [0..cs - 1] in
    ThisWeight $ fmap (\ (i, j) -> if i == j then 1 else 0) $
      WeightsDims $ WeightsDims $ WeightsData $ kronecker is is
