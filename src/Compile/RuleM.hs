{- Code for generating FGG rules, and the RuleM monad. -}

module Compile.RuleM (RuleM, addRuleBlock, runRuleM, getWeights, rulesToFGG) where
import qualified Data.Map as Map
import Control.Monad.Writer.Lazy
import Data.List (intercalate)
import Struct.Lib
import Util.FGG
import Util.Helpers
import Util.Tensor

type RuleM = Writer (Map EdgeLabel [HGF])

{- addRuleBlock lhs rhss

   A "rule block" is a set of rules, all with the same lhs and the
   same external nodes, that comprise all the rules with that lhs.

   If there is already a rule block with this lhs, the new rule block
   is discarded. (Theoretically the new rule block is identical to the
   old one, but we do not check this.) -}

addRuleBlock :: EdgeLabel -> [HGF] -> RuleM ()
addRuleBlock lhs rhss = tell (Map.singleton lhs rhss)

runRuleM :: RuleM () -> [Rule]
runRuleM rm =
  let ((), rs) = runWriter rm in
    [Rule lhs rhs | (lhs, rhss) <- Map.toList rs, rhs <- rhss]

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
  h (FaArrow tp1 tp2) = Just (getProdWeights [size tp1, size tp2])
  h (FaAddProd tps k) = Just (getSumWeights (size <$> tps) k)
  h (FaMulProd tps) = Just (getProdWeights (size <$> tps))
  h (FaCtor cs k) = Just (getCtorWeights size (cs !! k) cs)
  h (FaExtern _ _) = Nothing

{- rulesToFGG dom start rs nts facs

   Construct an FGG from:

   - dom: function that gives the possible Values belonging to d
   - start: start nonterminal
   - rs: list of rules
   - nts: list of nonterminal EdgeLabels and their "types"
   - facs: list of factors -}
             
rulesToFGG :: (NodeLabel -> Domain) -> EdgeLabel -> [NodeLabel] -> [Rule] -> FGG
rulesToFGG dom start start_type rs =
  FGG ds fs nts start (map checkRule rs)
  where
    -- Get all NodeLabels from start symbol and rule right-hand sides
    nls = concat (start_type : map (\ (Rule lhs (HGF ns es xs)) -> snds ns) rs)
    ds  = foldr (\ d m -> Map.insert d (dom d) m) Map.empty nls
    
    -- Get all EdgeLabels from both left-hand sides and right-hand
    -- sides. (The right-hand sides would be sufficient, but we want
    -- to check the left-hand sides for errors.)
    lhs_els = [(lhs, snds xs) | (Rule lhs (HGF _ es xs)) <- rs]
    rhs_es = concat [es | (Rule lhs (HGF _ es _)) <- rs]
    rhs_els = [(el, snds atts) | (Edge atts el) <- rhs_es]

    checkNonterm = \ x d1 d2 -> if d1 == d2 then d1 else error
      ("Conflicting types for nonterminal " ++ show x ++ ": " ++
        show d1 ++ " versus " ++ show d2)
    checkTerm = \ x (d1, w1) (d2, _) -> if d1 == d2 then (d1, w1) else error
      ("Conflicting types for terminal " ++ show x ++ ": " ++
        show d1 ++ " versus " ++ show d2)

    checkWeights el nls (Just w) =
      -- Compute expected shape, but after a 0, drop everything
      let shape = foldr (\ nl shape -> if null (dom nl) then [0] else length (dom nl) : shape) [] nls in
      if tensorShape w == shape then
        Just w
      else
        error ("Weight tensor for terminal " ++ show el ++ " has wrong shape (" ++ show (tensorShape w) ++ ", expected " ++ show shape ++ ")")
    checkWeights _ nls Nothing = Nothing

    checkRule r@(Rule lhs (HGF ns es xs)) =
      let count = Map.fromListWith (+) [(nn, 1) | (nn, nl) <- ns]
          dups = [nn | (nn, c) <- Map.toList count, c > 1] in
        if length dups > 0 then
          error ("Node(s) " ++ intercalate ", " (show <$> dups) ++ " appear more than once in rule for " ++ show lhs)
        else
          r

    sanitizeNonterms = \ (fs, nts) ->
      (fs, Map.filterWithKey (\ k _ -> not (k `Map.member` fs)) nts)

    (fs, nts) = sanitizeNonterms $
                foldr (\ (el, nls) (fs, nts) ->
                         case el of ElTerminal fac ->
                                      let w = checkWeights el nls (getWeights (length . dom) fac) in
                                          (Map.insertWith (checkTerm el) el (nls, w) fs, nts)
                                    ElNonterminal _ ->
                                      (fs, Map.insertWith (checkNonterm el) el nls nts))
                      (Map.empty, Map.fromList [(start, start_type)]) (lhs_els ++ rhs_els)
