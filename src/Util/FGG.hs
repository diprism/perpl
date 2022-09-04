{- A minimalist implementation of factor graph grammars (FGGs), which
   are the main target of the compiler. For more information about
   FGGs, see: David Chiang and Darcey Riley. Factor graph grammars. In
   Proc. NeurIPS, 6648–6658. 2020. -}

module Util.FGG (Node, NodeName(..), NodeLabel,
                  Domain, Value(..),
                  Edge(..), EdgeLabel(..),
                  Factor(..), Weights, Weight,
                  HGF(..), Rule(..), FGG(..), showFGG) where
import qualified Data.Map as Map
import Struct.Lib
import Util.Helpers
import Util.Tensor
import Util.JSON
import Data.List (intercalate)

type Domain = [Value]
newtype Value = Value String
  deriving Show
type Weight = Double
type Weights = Tensor Weight

{- Every node in an FGG has a NodeName, which is unique within its
   Rule. Nodes are either internal or external, and we use different
   NodeNames for the two kinds of nodes. -}

data NodeName =
    NnOut           -- external node holding the value of an expression
  | NnVar TmVar     -- external node holding the value of a free variable
  | NnInternal Int  -- internal node
  deriving (Eq, Ord)
instance Show NodeName where
  show NnOut = "*out*"
  show (NnVar v) = show v
  show (NnInternal i) = "*" ++ show i ++ "*"
  
{- Every node in an FGG has a NodeLabel, which determines a set, called
   a Domain, of possible Values that the node can have. For our
   purposes, a NodeLabel is always a Type, and the corresponding
   Domain is the set of String representations of all the inhabitants
   of that Type. -}

type NodeLabel = Type

{- Every Edge (really, a hyperedge) in an FGG has an EdgeLabel, which is
   either terminal or nonterminal.

   - Both terminals and nonterminals determine a list of NodeLabels of
     the attachment nodes. In the FGG literature, this list is called
     a "type," which we always write in scare quotes here.

   - Terminals determine a function, called a Factor, from the
     attachment nodes' Values to a Weight; here, this function is
     represented as a Tensor.

   - Edges labeled with nonterminals can be rewritten using
     Rules. Here, nonterminal labels always correspond to Terms. -}

data EdgeLabel =
    ElNonterminal Term
  | ElTerminal Factor
  deriving (Eq, Ord)
instance Show EdgeLabel where
  show (ElNonterminal tm) = show tm
  show (ElTerminal fac) = show fac

data Factor =
    FaScalar Weight                     -- just a scalar weight
  | FaIdentity Type                     -- identity matrix for tp
  | FaEqual Type Int                    -- k-way equality for tp
  | FaArrow Type Type                   -- tensor mapping (tp1, tp2) to tp1, tp2
  | FaAddProd [Type] Int                -- matrix projecting tp1+...+tpn to tpk
  | FaMulProd [Type]                    -- tensor mapping (tp1,...,tpn) to tp1,...,tpn
  | FaCtor [Ctor] Int                   -- k'th constructor in cs
  | FaExtern TmName Type                -- weights supplied externally
  deriving (Eq, Ord)
instance Show Factor where
  show (FaScalar w) = show w
  show (FaIdentity tp) = "Identity[" ++ show tp ++ "]"
  show (FaEqual tp n) = "Equal[" ++ show tp ++ "^" ++ show n ++ "]"
  show (FaArrow tp1 tp2) = "Arrow[" ++ show tp1 ++ "," ++ show tp2 ++ "]"
  show (FaAddProd tps k) = "AddProd[" ++ intercalate "," (show <$> tps) ++ ";" ++ show k ++ "]"
  show (FaMulProd tps) = "MulProd[" ++ intercalate "," (show <$> tps) ++ "]"
  show (FaCtor cs k) = show (cs !! k)
  show (FaExtern x _) = show x

type Node = (NodeName, NodeLabel)
data Edge = Edge { edge_atts :: [Node], edge_label :: EdgeLabel }
  deriving (Eq, Show)
-- Hypergraph fragment (= hypergraph with external nodes)
data HGF = HGF { hgf_nodes :: [Node], hgf_edges :: [Edge], hgf_exts :: [Node] }
  deriving (Eq, Show)
data Rule = Rule EdgeLabel HGF
  deriving (Eq, Show)
data FGG = FGG {
  domains :: Map NodeLabel Domain,                       -- node label to set of values
  factors :: Map EdgeLabel ([NodeLabel], Maybe Weights), -- edge label to att node labels, weights
  nonterminals :: Map EdgeLabel [NodeLabel],             -- nt name to attachment node labels
  start :: EdgeLabel,                                    -- start nt
  rules :: [Rule]                                        -- rules
}

-- Creates a JSON object from a weights tensor
weights_to_json :: Weights -> JSON
weights_to_json (Scalar n) = JSdouble n
weights_to_json (Vector ts) = JSarray [weights_to_json v | v <- ts]

{- fgg_to_json fgg

   Convert an FGG into a JSON. -}
                              
fgg_to_json :: FGG -> JSON
fgg_to_json (FGG ds fs nts s rs) =
  let mapToList = \ ds f -> JSobject $ map f (Map.toList ds) in
  JSobject
    [("grammar", JSobject 
      [("terminals", mapToList fs $
         \ (el, (d, mws)) -> (show el, JSobject [("type", JSarray [JSstring (show nl) | nl <- d])])),
       ("nonterminals", mapToList nts $
         \ (el, d) -> (show el, JSobject [
           ("type", JSarray [JSstring (show nl) | nl <- d])
         ])),
       ("start", JSstring (show s)),
       ("rules", JSarray $ flip map rs $
          \ (Rule lhs (HGF ns es xs)) ->
            let m = Map.fromList (zip (fsts ns) [0..]) in
            JSobject [
             ("lhs", JSstring (show lhs)),
             ("rhs", JSobject [
                 ("nodes", JSarray [JSobject [("label", JSstring (show d)), ("id", JSstring (show n))] | (n, d) <- ns]),
                 ("edges", JSarray $ flip map es $
                   \ (Edge atts el) -> JSobject [
                     ("attachments", JSarray [JSint (m Map.! n) | (n, d) <- atts]),
                     ("label", JSstring (show el))
                   ]),
                 ("externals", JSarray [JSint (m Map.! n) | (n, d) <- xs])
               ])
         ])
      ]),
    ("interpretation", JSobject [
       ("domains", mapToList ds $
         \ (nl, dom) -> (show nl, JSobject [
           ("class", JSstring "finite"),
           ("values", JSarray $ [JSstring v | Value v <- dom])
         ])),
       ("factors",
          let fs_filtered = Map.mapMaybe (\ (d, mws) -> maybe Nothing (\ ws -> Just (d, ws)) mws) fs in
          mapToList fs_filtered $
           \ (el, (d, ws)) -> (show el, JSobject [
             ("function", JSstring "finite"),
               ("type", JSarray [JSstring (show nl) | nl <- d]),
               ("weights", weights_to_json ws)
             ]))
        ])
    ]


showFGG :: FGG -> String
showFGG = pprint_json . fgg_to_json
