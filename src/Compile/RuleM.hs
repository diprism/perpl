{- Code for generating FGG rules, and the RuleM "monad-like" datatype -}

module Compile.RuleM where
import qualified Data.Map as Map
import Data.List
import Struct.Lib
import Util.FGG
import Util.Helpers
import Util.Tensor

type External = (NodeName, Type)

{- RuleM is a monad-like type for building FGGs.

   It stores the following:

   1. Map EdgeLabel HGF: rules, as a Map from lhs's to lists of rhs's
   2. [RHS]: a list of rhs's not yet inserted into (1)
   3. [External]: list of external nodes from the expression -}

data RuleM = RuleM [Rule] [External]

-- RuleM instances of >>= and >> (since not
-- technically a monad, need to pick new names)
infixl 1 +>=, +>, +>=*
-- Like (>>=) but for RuleM
-- Second arg receives as input the external nodes from the first arg
(+>=) :: RuleM -> ([External] -> RuleM) -> RuleM
RuleM rs xs +>= g =
  let RuleM rs' xs' = g xs in
    RuleM (rs ++ rs')
          (unionBy (\ (a, _) (a', _) -> a == a') xs xs')

-- Like (>>) but for RuleM
(+>) :: RuleM -> RuleM -> RuleM
r1 +> r2 = r1 +>= \ _ -> r2

-- Sequence together RuleMs, collecting each's externals
(+>=*) :: [RuleM] -> ([[External]] -> RuleM) -> RuleM
rs +>=* rf =
  let (r, xss) = foldl (\ (r, xss) r' -> let RuleM rs' xs' = r' in (r +> r', xs' : xss)) (returnRule, []) rs in
    r +> rf (reverse xss)

-- Add a list of external nodes
addExts :: [External] -> RuleM
addExts xs = RuleM [] xs

-- Add a single external node
addExt :: NodeName -> Type -> RuleM
addExt x tp = addExts [(x, tp)]

-- Add a list of rules
addRules :: [Rule] -> RuleM
addRules rs = RuleM rs []

-- Add a single rule
addRule :: Rule -> RuleM
addRule r = addRules [r]

-- Do nothing new
returnRule :: RuleM
returnRule = RuleM [] []

-- Removes all external nodes from a RuleM
resetExts :: RuleM -> RuleM
resetExts (RuleM rs xs) = RuleM rs []

-- Overrides the external nodes from a RuleM
setExts :: [External] -> RuleM -> RuleM
setExts xs (RuleM rs _) = RuleM rs xs

{--- Functions for computing Weights for terminal-labeled Edges ---}

{- getCtorWeights dom c cs

   Computes the weights for a specific constructor.

   - size: maps from node labels (Type) to sizes (Int)
   - c:    a specific constructor
   - cs:   list of all constructors (including c)

   Returns: If c = Ctor x ps, the tensor w[a1, ..., an, Ctor x as] = 1. -}

getCtorWeights :: (Type -> Int) -> Ctor -> [Ctor] -> Weights
getCtorWeights size (Ctor x as) cs =
  let ts = [if x' == x then tensorId (map size as) else zeros (map size as ++ [product (map size as')]) | Ctor x' as' <- cs] in
    tensorConcat (length as) ts

{- getIdWeights n

   -  n: number of possible values

   Returns: the nxn identity matrix -}
      
getIdWeights :: Int -> Weights
getIdWeights n = tensorId [n]

{- getSumWeights sizes

   Computes the weights for the direct sum of a list of domains.

   - sizes: the list of domain sizes

   Returns: If tp = tp1 + ... + tpn, the tensor w[x, in(i) x] = 1. -}

getSumWeights :: [Int] -> Int -> Weights
getSumWeights tpsizes k = let m = tpsizes !! k in
  tensorConcat 1 [if k == k' then tensorId [m] else zeros [m, size] | (k', size) <- enumerate tpsizes]

{- getProdWeights sizes

   Computes the weights for the tensor product of a list of domains.

   - sizes: the list of domain sizes

   If tp = (tp1, ..., tpn), returns the tensor w[x1, ..., xn, (x1, ..., xn)] = 1. -}
  
getProdWeights :: [Int] -> Weights
getProdWeights = tensorId

{- getEqWeights size n

   Returns the weights for (tm1 == tm2 == ... == tmn)

   - size: the size of the domains of the terms
   - n: the number of terms

   Returns: size x   ....   x s x 2 tensor
            |<- n copies ->|
 -}

getEqWeights :: Int -> Int -> Weights
getEqWeights size ntms =
  foldr
    (\ _ ws b mi -> Vector [ws (b && maybe True (== j) mi) (Just j) | j <- [0..size-1]])
    (\ b _ -> Vector (if b then [Scalar 0, Scalar 1] else [Scalar 1, Scalar 0]))
    [0..ntms-1]
    True
    Nothing

getWeights :: (Type -> Int) -> Factor -> Maybe Weights
getWeights size = h where
  h (FaScalar w) = Just (Scalar w)
  h (FaIdentity tp) = Just (getIdWeights (size tp))
  h (FaEqual tp n) = Just (getEqWeights (size tp) n)
  h (FaAddProd tps k) = Just (getSumWeights (size <$> tps) k)
  h (FaMulProd tps) = Just (getProdWeights (size <$> tps))
  h (FaCtor cs k) = Just (getCtorWeights size (cs !! k) cs)
  h (FaExtern _ _) = Nothing

{- rulesToFGG dom start rs nts facs

   Construct an FGG from:

   - dom: function that gives the possible Values belonging to d
   - start: start nonterminal
   - rs: list of rules with repetition counts
   - nts: list of nonterminal EdgeLabels and their "types"
   - facs: list of factors -}
             
rulesToFGG :: (NodeLabel -> Domain) -> EdgeLabel -> [NodeLabel] -> [Rule] -> FGG
rulesToFGG dom start start_type rs =
  FGG ds fs nts start rs
  where
    -- get all NodeLabels from start symbol and rule right-hand sides
    nls = concat (start_type : map (\ (Rule lhs (HGF ns es xs)) -> snds ns) rs)
    ds  = foldr (\ d m -> Map.insert d (dom d) m) Map.empty nls
    
    -- get all nonterminal EdgeLabels
    edges = concat [es | (Rule lhs (HGF _ es _)) <- rs]
    domsEq = \ x d1 d2 -> if d1 == d2 then d1 else error
      ("Conflicting types for nonterminal " ++ show x ++ ": " ++
        show d1 ++ " versus " ++ show d2)
    (fs, nts) = foldr (\ (Edge atts el) (fs, nts) ->
                         case el of ElTerminal fac ->
                                      let w = getWeights (length . dom) fac in
                                        (Map.insert el (snds atts, w) fs, nts)
                                    ElNonterminal _ ->
                                      (fs, Map.insertWith (domsEq el) el (snds atts) nts))
                      (Map.empty, Map.fromList [(start, start_type)]) edges
