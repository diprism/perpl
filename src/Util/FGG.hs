{- FGG datatype code -}

module Util.FGG where
import qualified Data.Map as Map
import Data.List
import Struct.Lib
import Util.Helpers
import Util.Tensor
import Util.JSON

-- Should the compiler make sure there aren't conflicting nonterminal domains?
-- This is only really a sanity check, and can be turned on/off as pleased
-- (though for the sake of efficiency, perhaps better off for stable releases)
checkDomsEq = True

type Domain = [Value] -- list of values for some type
newtype Value = Value String
type Factor = (EdgeLabel, Maybe Weights)
type Weight = Double
type Weights = Tensor Weight

data NodeName =
    NnOut           -- external node holding the value of an expression
  | NnVar Var       -- external node holding the value of a free variable
  | NnInternal Int  -- internal node
  deriving (Eq, Ord)
instance Show NodeName where
  show NnOut = "*out*"
  show (NnVar v) = v
  show (NnInternal i) = "*" ++ show i ++ "*"
  
type NodeLabel = Type

data EdgeLabel = ElNonterminal Term | ElTerminal String
  deriving (Eq, Ord)
instance Show EdgeLabel where
  show (ElNonterminal tm) = show tm
  show (ElTerminal s) = s

data Edge = Edge { edge_atts :: [(NodeName, NodeLabel)], edge_label :: EdgeLabel }
  deriving Eq
data HGF = HGF { hgf_nodes :: [(NodeName, NodeLabel)], hgf_edges :: [Edge], hgf_exts :: [(NodeName, NodeLabel)] }
  deriving Eq
data Rule = Rule EdgeLabel HGF
  deriving Eq
data FGG = FGG {
  domains :: Map NodeLabel Domain,                       -- node label to values
  factors :: Map EdgeLabel ([NodeLabel], Maybe Weights), -- edge label to att node labels, weights
  nonterminals :: Map EdgeLabel [NodeLabel],             -- nt name to attachment node labels
  start :: EdgeLabel,                                    -- start nt
  rules :: [(Int, Rule)]                                 -- [(reps, rule)]: reps keeps track of duplicate rules that should not be deduplicated
}

-- Take the union of two lists of factors
unionFactors :: [Factor] -> [Factor] -> [Factor]
unionFactors [] gs = gs
unionFactors ((x, tw) : fs) gs =
  let hs = unionFactors fs gs in
    maybe ((x, tw) : hs) (const hs) (lookup x hs)

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
       ("rules", JSarray $ concat $ flip map (nubBy (\ (_, r1) (_, r2) -> r1 == r2) rs) $
          \ (reps, Rule lhs (HGF ns es xs)) ->
            let m = Map.fromList (zip (fsts ns) [0..]) in
            replicate reps $ JSobject [
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

{- emptyFGG s

   An FGG with start nonterminal s and no rules. -}
emptyFGG :: EdgeLabel -> FGG
emptyFGG s = FGG Map.empty Map.empty Map.empty s []

{- rulesToFGG dom start rs nts facs

   Construct an FGG from:

   - dom: function that gives the possible Values belonging to d
   - start: start nonterminal
   - rs: list of rules with repetition counts
   - nts: list of nonterminal EdgeLabels and their "types"
   - facs: list of factors -}
             
rulesToFGG :: (NodeLabel -> Domain) -> EdgeLabel -> [(Int, Rule)] -> [(EdgeLabel, [NodeLabel])] -> [Factor] -> FGG
rulesToFGG dom start rs nts facs =
  FGG ds fs nts' start rsdom
  where
    rs' = nubBy (\ (_, r1) (_, r2) -> r1 == r2) rs
    rs'' = [r | (_, r) <- rs']
    rsdom = [(i, r) | (i, r) <- rs']

    nls = concat (map (\ (Rule lhs (HGF ns es xs)) -> snds ns) rs'') ++
          concat (snds nts)
    
    ds  = foldr (\ d m -> Map.insert d (dom d) m) Map.empty nls

    domsEq = \ x d1 d2 -> if not checkDomsEq || d1 == d2 then d1 else error
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
