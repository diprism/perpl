module FGG where
import qualified Data.Map as Map
import Data.List
import Ctxt
import Util
import Exprs

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
data PreWeight = ThisWeight Weights | PairWeight (String, String)
type Factor = (String, PreWeight)
type Prob = Double
data WeightsH x = WeightsData x | WeightsDims (WeightsH [x])
type Weights = WeightsH Prob
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

preWeightToWeight :: Map.Map String FType -> PreWeight -> Weights
preWeightToWeight ds (ThisWeight w) = w
preWeightToWeight ds (PairWeight (tp1, tp2)) =
  let Just vs1 = Map.lookup tp1 ds
      Just vs2 = Map.lookup tp2 ds in
--      Just vs12 = Map.lookup (tp1 ++ " -> " ++ tp2) ds in
    -- |vs1| x |vs2| x (|vs1|*|vs2|)
    WeightsDims $ WeightsDims $ WeightsDims $ WeightsData $
      map (map (\ v12 -> concat $ map (map $ \ v12' -> if v12 == v12' then 1 else 0) (kronecker vs1 vs2))) (kronecker vs1 vs2)

scalarWeight = WeightsData
vectorWeight = WeightsDims . WeightsData
matrixWeight = WeightsDims . WeightsDims . WeightsData
scalarPreWeight = ThisWeight . scalarWeight
vectorPreWeight = ThisWeight . vectorWeight
matrixPreWeight = ThisWeight . matrixWeight

-- Construct an FGG from a list of rules, a start symbol,
-- and a function that gives the possible values of each type
rulesToFGG :: (Type -> [String]) -> String -> [Rule] -> [Nonterminal] -> [Factor] -> FGG_JSON
rulesToFGG doms start rs nts facs =
  let rs' = nub rs
      ds  = foldr (\ (Rule lhs (HGF ns es xs)) m ->
                     foldr (\ n -> Map.insert (show n) (doms n)) m ns) Map.empty rs'
      nts'' = foldr (\ (x, tp) -> Map.insert x [show tp]) Map.empty nts
      nts' = foldr (\ (Rule lhs (HGF ns _ xs)) ->
                      Map.insert lhs (map (\ i -> show $ ns !! i) xs)) nts'' rs'
      facs' = map (\ (x, w) -> (x, preWeightToWeight ds w)) facs
      getFac = \ l -> maybe (error ("In rulesToFGG, no factor named " ++ l ++ " (factor names: " ++ show (map fst facs) ++ ", nts:" ++ show (Map.keys nts') ++ ")"))
                        id $ lookup l facs'
      fs  = foldr (\ (Rule lhs (HGF ns es xs)) m ->
                     foldr (\ (Edge atts l) -> let lnodes = map ((!!) ns) atts in
                               if Map.member l nts' then id else
                                 Map.insert l (map show lnodes, getFac l))
                           m es)
                  Map.empty rs' in
    FGG_JSON ds fs nts' start rs'


{-example_ctxt :: Ctxt
example_ctxt = ctxtDeclType (ctxtDeclType emptyCtxt "W" (map (\ x -> Ctor x []) ["the", "cat", "sat", "on", "mat"])) "T" (map (\ x -> Ctor x []) ["DT", "NN", "VBD", "IN", "BOS", "EOS"])

example_rule1 = Rule "S"
  (HGF ["T"] [Edge [0] "is_bos",
              Edge [0] "X"] [])
example_rule2 = Rule "X"
  (HGF ["T", "T", "W"] [Edge [0, 1] "transition",
                        Edge [1, 2] "emission",
                        Edge [1] "X"] [0])
example_rule3 = Rule "X"
  (HGF ["T", "T"] [Edge [0, 1] "transition",
                   Edge [1] "is_eos"] [0])

example_fgg = rulesToFGG (maybe [] (map $ \ (Ctor x as) -> x) . ctxtLookupType example_ctxt) "S" [example_rule1, example_rule2, example_rule3]
-}
{-
example_fgg :: FGG_JSON
example_fgg = FGG_JSON
  (Map.fromList [("T", ["DT", "NN", "VBD", "IN", "BOS", "EOS"]), ("W", ["the", "cat", "sat", "on", "mat"])])
  (Map.fromList [("transition", (["T", "T"], WeightsDims (WeightsDims (WeightsData [[0, 1, 0, 0, 0, 0],[0, 0.25, 0.25, 0.25, 0, 0.25],[0.3, 0, 0, 0.3, 0, 0.4],[1, 0, 0, 0, 0, 0],[0.8, 0, 0, 0.2, 0, 0],[0, 0, 0, 0, 0, 0]])))),
                 ("emission", (["T", "W"], WeightsDims (WeightsDims (WeightsData [[1, 0, 0, 0, 0], [0, 0.5, 0, 0, 0.5], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]])))),
                 ("is_bos", (["T"], WeightsDims (WeightsData [0, 0, 0, 0, 1, 0]))),
                 ("is_eos", (["T"], WeightsDims (WeightsData [0, 0, 0, 0, 0, 1])))])
  (Map.fromList [("S", []), ("X", ["T"])])
  "S"
  [Rule "S" (HGF ["T"] [Edge [0] "is_bos", Edge [0] "X"] []),
   Rule "X" (HGF ["T", "T", "W"] [Edge [0, 1] "transition", Edge [1, 2] "emission", Edge [1] "X"] [0]),
   Rule "X" (HGF ["T", "T"] [Edge [0, 1] "transition", Edge [1] "is_eos"] [0])]
-}
