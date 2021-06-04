module FGG where
import qualified Data.Map as Map
import Exprs
--import System.Posix.Escape.Unicode


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

{-
type LV = String -- Vertex label
type LE = String -- Hyperedge label
type Node = Int
type Hyperedge = Int
newtype Hypergraph = Hypergraph {
  hgV    :: [Node],
  hgE    :: [Hyperedge],
  hgatt  :: Map.Map Hyperedge [Node],
  hgvlab :: Map.Map Node LV,
  hgelab :: Map.Map Hyperedge LE,
  hgext  :: [Node],
}
{- newtype HypergraphFrag = HypergraphFrag {
  hgfHG  :: Hypergraph,
  hgfext :: [Node],
} -}
newtype FactorGraph = FactorGraph {
  fgHG :: Hypergraph,
  fgOmega :: (),
  fgF :: Real r => [] -> r
}
newtype HyperedgeReplacementGraph = HyperedgeRaplacementGraph {
  hrgN :: [LE],
  hrgT :: [LE],
  hrgP :: [(LE -> Hypergraph)],
  hrgS :: LE,
}
-}

type Domain = [String]
data NodeLabel = NodeLabel { node_name :: String, node_domain :: Domain }
data EdgeLabel = EdgeLabel { edge_name :: String, edge_is_terminal :: Bool, edge_node_labels :: [NodeLabel] }
type Value = String
type FType = [Value]
type Prob = Double

data WeightsH x = WeightsData x | WeightsDims (WeightsH [x])
type Weights = WeightsH Prob



data Edge = Edge { edge_atts :: [Int], edge_label :: String }

data HGF = HGF { hgf_nodes :: [String], hfg_edges :: [Edge], hfg_exts :: [Int]}

data Rule = Rule String HGF

data FGG_JSON = FGG_JSON {
  domains :: Map.Map String FType,
  factors :: Map.Map String (Domain, Weights),
  nonterminals :: Map.Map String Domain,
  start :: String, -- NodeLabel with node_domain = []
  rules :: [Rule]
}

weights_to_json_h :: WeightsH x -> (x -> JSON) -> JSON
weights_to_json_h (WeightsData p) f = f p
weights_to_json_h (WeightsDims ws) f = weights_to_json_h ws (JSarray . map f)

weights_to_json :: Weights -> JSON
weights_to_json ws = weights_to_json_h ws JSdouble

join_list :: Show a => [a] -> String
join_list [] = ""
join_list (a : []) = show a
join_list (a : as) = show a ++ "," ++ join_list as

join_dict :: Show a => [(String, a)] -> String
join_dict [] = ""
join_dict ((k, v) : []) = show k ++ ":" ++ show v
join_dict ((k, v) : kvs) = show k ++ ":" ++ show v ++ "," ++ join_dict kvs

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

     ("rules", JSarray $ flip map rs $
       \ (Rule lhs (HGF ns es xs)) -> JSobject [
           ("lhs", JSstring lhs),
           ("rhs", JSobject [
               ("nodes", JSarray $ map JSstring ns),
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

emptyFGG :: String -> FGG_JSON
emptyFGG s = FGG_JSON Map.empty Map.empty Map.empty s []

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
