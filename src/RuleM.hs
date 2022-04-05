module RuleM where
import Data.List
import qualified Data.Map as Map
import Exprs
import FGG
import Util
import Name
import Tensor

-- RuleM monad-like datatype and functions
type External = (Var, Type)
data RuleM = RuleM [(Int, Rule)] [External] [Nonterminal] [Factor]

-- RuleM instances of >>= and >= (since not
-- technically a monad, need to pick new names)
infixl 1 +>=, +>, +>=*
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
(+>=*) :: [RuleM] -> ([[External]] -> RuleM) -> RuleM
rs +>=* rf =
  let (r, xss) = foldl (\ (r, xss) r' -> let RuleM rs' xs' nts' fs' = r' in (r +> r', xs' : xss)) (returnRule, []) rs in
    r +> rf (reverse xss)

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
addRules :: [(Int, Rule)] -> RuleM
addRules rs = RuleM rs [] [] []

-- Add a single rule
addRule :: Int -> Rule -> RuleM
addRule reps r = addRules [(reps, r)]

castHGF :: HGF' -> HGF
castHGF (HGF' ns es xs) =
  let (ns', [ins]) = combineExts [ns]
      m = Map.fromList [(v, ins !! i) | ((v, tp), i) <- zip ns' ins] in
    HGF (snds ns)
      [Edge [m Map.! v | (v, tp) <- as] l | Edge' as l <- es]
      (nub [m Map.! v | (v, tp) <- xs])

addIncompleteFactor :: Var -> RuleM
addIncompleteFactor x = RuleM [] [] [] [(x, Nothing)]

addFactor :: Var -> Weights -> RuleM
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

-- Returns if this lhs is already used
isRule :: String -> RuleM -> Bool
isRule lhs (RuleM rs xs nts fs) = any (\ (_, Rule lhs' _) -> lhs == lhs') rs

-- Returns the Weights for a function tp1 -> tp2
getPairWeights :: Int -> Int -> Weights
getPairWeights tp1s tp2s = tensorId [tp1s, tp2s]

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
  zeros ([length (dom tp) | tp <- ps] ++ [length (dom tp)])

-- Computes the weights for a list of constructors
getCtorWeightsAll :: (Type -> [String]) -> [Ctor] -> Type -> [(String, Weights)]
getCtorWeightsAll dom cs y =
  concat [[(ctorFactorName x [(TmVarL x atp, atp) | (x, atp) <- zip as' as] y, ws)
          | (as', ws) <- getCtorWeights dom (Ctor x as) cs]
         | Ctor x as <- cs]
  

-- Computes the weights for a specific constructor
getCtorWeights :: (Type -> [String]) -> Ctor -> [Ctor] -> [([String], Weights)]
getCtorWeights dom (Ctor x as) cs =
  let (cs_before, cs_after) = splitCtorsAt cs x
      csf = \ cs' -> sum [product (map (length . dom) as') | (Ctor x' as') <- cs']
      cs_b' = csf cs_before
      cs_a' = csf cs_after
      mkrow = \ mask -> vector (replicate cs_b' 0 ++ mask ++ replicate cs_a' 0)
  in
    flip map (kronpos (map dom as)) $ \ as' -> (,) [a | (_, _, a) <- as'] $
      let (out, pos) = foldr (\ (i, o, _) (l, j) -> (l * o, l * i + j)) (1, 0) as'
          row = mkrow (tensorIdRow pos out) in
      foldr (\ (i, o, a) ws -> Vector [if i == j then ws else fmap (\ _ -> 0) ws | j <- [0..o - 1]]) row as'

-- Computes the weights for a specific constructor (can't remember how this is different from getCtorWeights above :P)
getCtorWeightsFlat :: (Type -> [String]) -> Ctor -> [Ctor] -> Weights
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

-- Identity matrix
getCtorEqWeights :: Int {- num of possible values -} -> Weights
getCtorEqWeights cs = tensorId [cs]

getAmpWeights :: (Type -> [String]) -> [Type] -> [Weights]
getAmpWeights dom tps =
  let tpvs = map dom tps in
    [Vector
      (concatMap
        (\ (j, vs) ->
            [Vector [Scalar (if l == k && i == j then 1 else 0) | (l, _) <- enumerate itpvs] | (k, _) <- enumerate vs]) (enumerate tpvs)) | (i, itpvs) <- enumerate tpvs]

getProdWeights :: [[String]] -> [([String], Weights)]
getProdWeights tpvs =
  [([a | (_, _, a) <- as'],
    let (out, pos) = foldr (\ (i, o, _) (l, j) -> (l * o, l * i + j)) (1, 0) as' in
      foldr (\ (i, o, a) ws ->
               Vector [if i == j then ws else fmap (\ _ -> 0) ws | j <- [0..o - 1]])
        (vector (tensorIdRow pos out)) as')
  | as' <- kronpos tpvs]

getProdWeightsV :: [[String]] -> Weights
getProdWeightsV tpvs = tensorId [length vs | vs <- tpvs]

getEqWeights :: Int -> Int -> Weights
getEqWeights dom ntms =
  foldr
    (\ _ ws b mi -> Vector [ws (b && maybe True (== j) mi) (Just j) | j <- [0..dom-1]])
    (\ b _ -> Vector (if b then [Scalar 0, Scalar 1] else [Scalar 1, Scalar 0]))
    [0..ntms-1]
    True
    Nothing
--  Vector [foldr
--            (\ _ ws b -> Vector [ws (b && i == j) | j <- [0..dom-1]])
--            (\ b -> Vector (if b then [Scalar 0, Scalar 1] else [Scalar 1, Scalar 0]))
--            [1..dom - 1] True
--          | i <- [0..dom - 1]]

-- TODO: it is no longer necessary to be this complex—now the we just need
-- to take and return a single (non-nested) list

-- Given a set of external nodes, this returns a pair where the first
-- is basically just the nub of the concatenated nodes, and the second
-- is a mapping from each node's original position to its new one in
-- the first part.
-- It takes a list of lists to allow you to more easily keep track of
-- where an arbitrary number of externals went.
combineExts :: Ord a => [[(a, x)]] -> ([(a, x)], [[Int]])
combineExts = h Map.empty 0 where

  index :: Ord a => Map a Int -> Int -> [(a, x)] -> (Map a Int, [(a, x)])
  index ixs i [] = (ixs, [])
  index ixs i (a : as) = case Map.lookup (fst a) ixs of
    Nothing -> fmap ((:) a) (index (Map.insert (fst a) i ixs) (succ i) as)
    Just ia -> index ixs i as
  
  h :: Ord a => Map a Int -> Int -> [[(a, x)]] -> ([(a, x)], [[Int]])
  h ixs i [] = ([], [])
  h ixs i (as : rest) =
    let (ixs', as') = index ixs i as
        is = [ixs' Map.! a | (a, _) <- as]
        (rs, ms) = h ixs' (i + length as') rest in
      (as' ++ rs, is : ms)

