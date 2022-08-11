{- Code for generating FGG rules, and the RuleM "monad-like" datatype -}

module Compile.RuleM where
import qualified Data.Map as Map
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
type Terminal = (EdgeLabel, Maybe Weights)

-- RuleM stores the following:
--   1. [(Int, Rule)]: a list of rules and how many times to duplicate them
--                            (so amb True False True => p(True) = **2**, p(False) = 1)
--   2. [External]: list of external nodes from the expression
--   3. [Nonterminal]: nonterminal accumulator
--   4. [Terminal]: terminal/factor accumulator
data RuleM = RuleM [(Int, Rule)] [External] [Nonterminal] [Terminal]

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

-- Take the union of two lists of terminals
unionFactors :: [Terminal] -> [Terminal] -> [Terminal]
unionFactors [] gs = gs
unionFactors ((x, tw) : fs) gs =
  let hs = unionFactors fs gs in
    maybe ((x, tw) : hs) (const hs) (lookup x hs)

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

{- getCtorWeights dom c cs

   Computes the weights for a specific constructor.

   - dom: maps from node labels (Type) to domains ([Value])
   - c:   a specific constructor
   - cs:  list of all constructors (including c)

   Returns: If c = Ctor x ps, the tensor w[a1, ..., an, Ctor x as] = 1. -}

getCtorWeights :: (Type -> [Value]) -> Ctor -> [Ctor] -> Weights
getCtorWeights dom (Ctor x as) cs =
  let shape = map (length . dom)
      ts = [if x' == x then tensorId (shape as) else zeros (shape as ++ [product (shape as')]) | Ctor x' as' <- cs] in
    tensorConcat (length as) ts

{- getIdWeights n

   -  n: number of possible values

   Returns: the nxn identity matrix -}
      
getIdWeights :: Int -> Weights
getIdWeights n = tensorId [n]

{- getSumWeights tpvs

   Computes the weights for the direct sum of a list of domains.

   - tpvs: the list of domains

   Returns: If tp = tp1 + ... + tpn, the tensor w[x, in(i) x] = 1. -}

getSumWeights :: [[Value]] -> Int -> Weights
getSumWeights tpvs k = let m = length (tpvs !! k) in
  tensorConcat 1 [if k == k' then tensorId [m] else zeros [m, length d] | (k', d) <- enumerate tpvs]

{- getProdWeights tpvs

   Computes the weights for the tensor product of a list of domains.

   - tpvs: the list of domains

   If tp = (tp1, ..., tpn), returns the tensor w[x1, ..., xn, (x1, ..., xn)] = 1. -}
  
getProdWeights :: [[Value]] -> Weights
getProdWeights tpvs = tensorId [length vs | vs <- tpvs]

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

{- rulesToFGG dom start rs nts facs

   Construct an FGG from:

   - dom: function that gives the possible Values belonging to d
   - start: start nonterminal
   - rs: list of rules with repetition counts
   - nts: list of nonterminal EdgeLabels and their "types"
   - facs: list of factors -}
             
rulesToFGG :: (NodeLabel -> Domain) -> EdgeLabel -> [(Int, Rule)] -> [(EdgeLabel, [NodeLabel])] -> [Terminal] -> FGG
rulesToFGG dom start rs nts facs =
  FGG ds fs nts' start rs'
  where
    rs' = nubBy (\ (_, r1) (_, r2) -> r1 == r2) rs
    rs'' = [r | (_, r) <- rs']

    nls = concat (map (\ (Rule lhs (HGF ns es xs)) -> snds ns) rs'') ++
          concat (snds nts)
    
    ds  = foldr (\ d m -> Map.insert d (dom d) m) Map.empty nls

    domsEq = \ x d1 d2 -> if d1 == d2 then d1 else error
      ("Conflicting types for nonterminal " ++ show x ++ ": " ++
        show d1 ++ " versus " ++ show d2)

    -- Nonterminals that were added directly by addNonterm(s)
    nts'' = Map.fromList nts

    -- Nonterminals from left-hand sides of rules get their "type" from the external nodes
    nts' = foldr (\ (Rule lhs (HGF ns _ xs)) ->
                    Map.insertWith (domsEq lhs) lhs (snds xs)) nts'' rs''

    getFac = \ l lhs -> maybe (error ("In the rule " ++ show lhs ++ ", no factor named " ++ show l))
                      id $ lookup l facs

    fs  = foldr (\ (Rule lhs (HGF ns es xs)) m ->
                   foldr (\ (Edge atts l) ->
                             if Map.member l nts' then id else
                               Map.insert l (snds atts, getFac l lhs))
                         m es)
                Map.empty rs''
