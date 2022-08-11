{- Code for generating FGG rules, and the RuleM "monad-like" datatype -}

module Compile.RuleM where
import Data.List
import Struct.Lib
import Util.FGG
import Util.Helpers
import Util.Tensor

{- RuleM is a monad-like type for building FGGs.

   TODO: Its contents are not that different from FGG itself; could they be merged?
 -}

type External = (NodeName, Type)
type Nonterminal = (EdgeLabel, [Type])
-- RuleM stores the following:
--   1. [(Int, Rule)]: a list of rules and how many times to duplicate them
--                            (so amb True False True => p(True) = **2**, p(False) = 1)
--   2. [External]: list of external nodes from the expression
--   3. [Nonterminal]: nonterminal accumulator
--   4. [Factor]: factor accumulator
data RuleM = RuleM [(Int, Rule)] [External] [Nonterminal] [Factor]

-- RuleM instances of >>= and >> (since not
-- technically a monad, need to pick new names)
infixl 1 +>=, +>, +>=*
-- Like (>>=) but for RuleM
-- Second arg receives as input the external nodes from the first arg
(+>=) :: RuleM -> ([External] -> RuleM) -> RuleM
RuleM rs xs nts fs +>= g =
  let RuleM rs' xs' nts' fs' = g xs in
    RuleM (rs ++ rs')
          (unionBy (\ (a, _) (a', _) -> a == a') xs xs')
          (nts ++ nts')
          (unionFactors fs fs')

-- Like (>>) but for RuleM
(+>) :: RuleM -> RuleM -> RuleM
r1 +> r2 = r1 +>= \ _ -> r2

-- Sequence together RuleMs, collecting each's externals
(+>=*) :: [RuleM] -> ([[External]] -> RuleM) -> RuleM
rs +>=* rf =
  let (r, xss) = foldl (\ (r, xss) r' -> let RuleM rs' xs' nts' fs' = r' in (r +> r', xs' : xss)) (returnRule, []) rs in
    r +> rf (reverse xss)

-- Add a list of external nodes
addExts :: [External] -> RuleM
addExts xs = RuleM [] xs [] []

-- Add a single external node
addExt :: NodeName -> Type -> RuleM
addExt x tp = addExts [(x, tp)]

-- Add a list of nonterminals with the types of their attachment nodes
addNonterms :: [Nonterminal] -> RuleM
addNonterms nts = RuleM [] [] nts []

-- Add a single nonterminal with the types of its attachment nodes
addNonterm :: EdgeLabel -> [Type] -> RuleM
addNonterm x tps = addNonterms [(x, tps)]

-- Add a list of rules
addRules :: [(Int, Rule)] -> RuleM
addRules rs = RuleM rs [] [] []

-- Add a single rule
addRule :: Int -> Rule -> RuleM
addRule reps r = addRules [(reps, r)]

-- Adds an "incomplete" factor (extern)
addIncompleteFactor :: EdgeLabel -> RuleM
addIncompleteFactor x = RuleM [] [] [] [(x, Nothing)]

-- Adds a factor x with weights tensor w
addFactor :: EdgeLabel -> Weights -> RuleM
addFactor x w = RuleM [] [] [] [(x, Just w)]

-- Do nothing new
returnRule :: RuleM
returnRule = RuleM [] [] [] []

-- Removes all external nodes from a RuleM
resetExts :: RuleM -> RuleM
resetExts (RuleM rs xs nts fs) = RuleM rs [] nts fs

-- Overrides the external nodes from a RuleM
setExts :: [External] -> RuleM -> RuleM
setExts xs (RuleM rs _ nts fs) = RuleM rs xs nts fs

{--- Functions for computing Weights for terminal-labeled Edges ---}

{- getPairWeights tp1s tp2s

   Returns the weights w[x,y,(x,y)] = 1, which is used for function
   types tp1 -> tp2.  tp1s and tp2s are the sizes of the domains of x1
   and x2, respectively. -}
                                 
getPairWeights :: Int -> Int -> Weights
getPairWeights tp1s tp2s = tensorId [tp1s, tp2s]

{- getCtorWeightsFlat dom c cs

   Computes the weights for a specific constructor.

   - dom: maps from node labels (Type) to domains ([Value])
   - c:   a specific constructor
   - cs:  list of all constructors (including c)

   Returns: If c = Ctor x ps, the tensor w[a1, ..., an, Ctor x as] = 1. -}

getCtorWeightsFlat :: (Type -> [Value]) -> Ctor -> [Ctor] -> Weights
getCtorWeightsFlat dom (Ctor x as) cs =
  let (cs_before, cs_after) = splitCtorsAt cs x
      csf = \ cs' -> sum [product (map (length . dom) as') | Ctor x' as' <- cs']
      cs_b' = csf cs_before
      cs_a' = csf cs_after
      mkrow = \ mask -> replicate cs_b' 0 ++ mask ++ replicate cs_a' 0
  in
    foldr
      (\ avs jl2ws j l -> Vector [jl2ws (l * i + j) (l * length avs) | i <- [0..length avs - 1]])
      (\ j l -> vector (mkrow (tensorIdRow j l)))
      (map dom as) 0 1

{- getIdWeights n

   -  n: number of possible values

   Returns: the nxn identity matrix -}
      
getIdWeights :: Int  -> Weights
getIdWeights n = tensorId [n]

{- getAmpWeights tpvs

   Computes the weights for the additive product of a list of domains.

   - tpvs: the list of domains

   Returns: If tp = <tp1, ..., tpn>, a list of weights [w1, ..., wn] where
   wi[x, <_, ..., x, ..., _>] = 1. -}

getAmpWeights :: [[Value]] -> [Weights]
getAmpWeights tpvs =
  [Vector
    (concatMap
      (\ (j, vs) ->
          [Vector [Scalar (if l == k && i == j then 1 else 0) | (l, _) <- enumerate itpvs] | (k, _) <- enumerate vs]) (enumerate tpvs)) | (i, itpvs) <- enumerate tpvs]

{- getProdWeightsV tpvs

   Computes the weights for the multiplicative product of a list of domains.

   - tpvs: the list of domains

   If tp = (tp1, ..., tpn), returns the tensor w[x1, ..., xn, (x1, ..., xn)] = 1. -}
  
getProdWeightsV :: [[Value]] -> Weights
getProdWeightsV tpvs = tensorId [length vs | vs <- tpvs]

{- getEqWeights s n

   Returns the weights for (tm1 == tm2 == ... == tmn)

   - s: the size of the domains of the terms
   - n: the number of terms

   Returns: s x   ....   x s x 2 tensor
            |<- n copies ->|
 -}

getEqWeights :: Int -> Int -> Weights
getEqWeights dom ntms =
  foldr
    (\ _ ws b mi -> Vector [ws (b && maybe True (== j) mi) (Just j) | j <- [0..dom-1]])
    (\ b _ -> Vector (if b then [Scalar 0, Scalar 1] else [Scalar 1, Scalar 0]))
    [0..ntms-1]
    True
    Nothing
