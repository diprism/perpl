module FGG where
import qualified Data.Map as Map
import Data.List
import Ctxt
import Util
import Exprs
import Show
import Name
import Tensor

-- Should the compiler make sure there aren't conflicting nonterminal domains?
checkDomsEq = True

{- ====== JSON Functions ====== -}

data JSON =
    JSnull
  | JSbool Bool
  | JSint Int
  | JSdouble Double
  | JSstring String
  | JSarray [JSON]
  | JSobject [(String, JSON)]

instance Show JSON where
  show JSnull = "null"
  show (JSbool b) = if b then "true" else "false"
  show (JSint i) = show i
  show (JSdouble d) = show d
  show (JSstring s) = show s
  show (JSarray js) = '[' : (join_list js ++ "]")
  show (JSobject kvs) = '{' : (join_dict kvs ++ "}")


{- ====== FGG Functions ====== -}

type Nonterminal = (Var, Type)
type Domain = [String]
type Value = String
type FType = [Value]
type Factor = (String, Weights)
type Prob = Double
data WeightsH x = WeightsData x | WeightsDims (WeightsH [x])
data WeightsH' x = WeightsData' x | WeightsDims' [WeightsH' x]
type Weights = WeightsH Prob
type Weights' = WeightsH' Prob
data Edge = Edge { edge_atts :: [Int], edge_label :: String }
  deriving Eq
data HGF = HGF { hgf_nodes :: [Type], hfg_edges :: [Edge], hfg_exts :: [Int]}
  deriving Eq
data Rule = Rule String HGF
  deriving Eq
data FGG_JSON = FGG_JSON {
  domains :: Map.Map String FType,
  factors :: Map.Map String (Domain, Weights),
  nonterminals :: Map.Map String Domain,
  start :: String,
  rules :: [Rule]
}

concatFactors :: [Factor] -> [Factor] -> [Factor]
concatFactors [] gs = gs
concatFactors ((x, w) : fs) gs =
  let hs = concatFactors fs gs in
    maybe ((x, w) : hs) (\ _ -> hs) (lookup x gs)

weights_to_json_h :: WeightsH x -> (x -> JSON) -> JSON
weights_to_json_h (WeightsData p) f = f p
weights_to_json_h (WeightsDims ws) f = weights_to_json_h ws (JSarray . map f)

weights_to_json :: Weights -> JSON
weights_to_json ws = weights_to_json_h ws JSdouble

instance Functor WeightsH where
  fmap f (WeightsData x) = WeightsData $ f x
  fmap f (WeightsDims x) = WeightsDims $ fmap (map f) x

-- Print a comma-separated list
join_list :: Show a => [a] -> String
join_list [] = ""
join_list (a : []) = show a
join_list (a : as) = show a ++ "," ++ join_list as

-- Print a comma-separated key-value dict
join_dict :: Show a => [(String, a)] -> String
join_dict [] = ""
join_dict ((k, v) : []) = show k ++ ":" ++ show v
join_dict ((k, v) : kvs) = show k ++ ":" ++ show v ++ "," ++ join_dict kvs

-- Convert an FGG into a JSON
fgg_to_json :: FGG_JSON -> JSON
fgg_to_json (FGG_JSON ds fs nts s rs) =
  let mapToList = \ ds f -> JSobject $ Map.toList $ fmap f ds in
  JSobject
    [("domains", mapToList ds $
       \ ds' -> JSobject [
         ("class", JSstring "finite"),
         ("values", JSarray $ map JSstring ds')
       ]),
      
     ("factors", mapToList fs $
       \ (d, ws) -> JSobject [
         ("function", JSstring "categorical"),
         ("type", JSarray $ map JSstring d),
         ("weights", weights_to_json ws)
       ]),
      
     ("nonterminals", mapToList nts $
       \ d -> JSobject [
         ("type", JSarray $ map JSstring d)
       ]),

     ("start", JSstring s),

     ("rules", JSarray $ flip map (nub rs) $
       \ (Rule lhs (HGF ns es xs)) -> JSobject [
           ("lhs", JSstring lhs),
           ("rhs", JSobject [
               ("nodes", JSarray $ map (\ n -> JSobject [("label", JSstring (show n))]) ns),
               ("edges", JSarray $ flip map es $
                 \ (Edge atts l) -> JSobject [
                   ("attachments", JSarray (map JSint atts)),
                   ("label", JSstring l)
                 ]),
               ("externals", JSarray $ map JSint xs)
             ])
       ])
    ]

instance Show FGG_JSON where
  show = show . fgg_to_json


-- Default FGG
emptyFGG :: String -> FGG_JSON
emptyFGG s = FGG_JSON Map.empty Map.empty Map.empty s []


-- Pulls the data from a WeightsH
invWeightsData :: WeightsH a -> a
invWeightsData (WeightsData ws) = ws
invWeightsData (WeightsDims ws) = error "In invWeightsData, expected WeightsData"

-- Takes the dims from a WeightsH
invWeightsDims :: WeightsH a -> WeightsH [a]
invWeightsDims (WeightsDims ws) = ws
invWeightsDims (WeightsData ws) = error "In invWeightsDims, expected WeightsDims"

-- Pushes WeightsH into each of its elements
weightsPush :: WeightsH [a] -> [WeightsH a]
weightsPush (WeightsData ws) = map WeightsData ws
weightsPush (WeightsDims ws) = map WeightsDims (weightsPush ws)

weightsPush' :: WeightsH' [a] -> [WeightsH' a]
weightsPush' (WeightsData' ws) = map WeightsData' ws
weightsPush' (WeightsDims' ws) = [WeightsDims' (weightsPush' w) | w <- ws]

-- Pulls a the weights from a list into a WeightsH
weightsPull :: [WeightsH a] -> WeightsH [a]
weightsPull [] = WeightsData []
weightsPull (WeightsData ws : ws') =
  WeightsData (map invWeightsData (WeightsData ws : ws'))
weightsPull (WeightsDims ws : ws') =
  let ws'' = map invWeightsDims (WeightsDims ws : ws') in
  WeightsDims $ weightsPull ws''

weightsTo' :: WeightsH x -> WeightsH' x
weightsTo' (WeightsData x) = WeightsData' x
weightsTo' (WeightsDims xs) = WeightsDims' (let w = weightsTo' xs in weightsPush' w)

weights'To :: WeightsH' x -> WeightsH x
weights'To (WeightsData' x) = WeightsData x
weights'To (WeightsDims' xs) = WeightsDims (weightsPull [weights'To x | x <- xs])

scalarWeight = WeightsData
vectorWeight = WeightsDims . WeightsData
matrixWeight = WeightsDims . WeightsDims . WeightsData

tensorToWeights' :: Tensor a -> WeightsH' a
tensorToWeights' (Scalar a) = WeightsData' a
tensorToWeights' (Vector ts) = WeightsDims' [tensorToWeights' t | t <- ts]

tensorToWeights :: Tensor a -> WeightsH a
tensorToWeights = weights'To . tensorToWeights'

-- Construct an FGG from a list of rules, a start symbol,
-- and a function that gives the possible values of each type
rulesToFGG :: (Type -> [String]) -> String -> [Rule] -> [Nonterminal] -> [Factor] -> FGG_JSON
rulesToFGG doms start rs nts facs =
  let rs' = nub rs
      ds  = foldr (\ (Rule lhs (HGF ns es xs)) m ->
                     foldr (\ n -> Map.insert (show n) (doms n)) m ns) Map.empty rs'
      domsEq = \ x d1 d2 -> if not checkDomsEq || d1 == d2 then d1 else error
        ("Conflicting domains for nonterminal " ++ x ++ ": " ++
          show d1 ++ " vs " ++ show d2)
      nts'' = foldr (\ (x, tp) -> Map.insert x [show tp]) Map.empty nts
      nts' = foldr (\ (Rule lhs (HGF ns _ xs)) ->
                      Map.insertWith (domsEq lhs) lhs [show (ns !! i) | i <- xs]) nts'' rs'
      getFac = \ l lhs -> maybe (error ("In the rule " ++ lhs ++ ", no factor named " ++ l))
                        id $ lookup l facs
      fs  = foldr (\ (Rule lhs (HGF ns es xs)) m ->
                     foldr (\ (Edge atts l) ->
                               if Map.member l nts' then id else
                                 Map.insert l ([show (ns !! i) | i <- atts], getFac l lhs))
                           m es)
                  Map.empty rs'
  in
    FGG_JSON ds fs nts' start rs'
