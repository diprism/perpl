{- FGG datatype code -}

module Util.FGG where
import qualified Data.Map as Map
import Data.List
import Util.Helpers
import Util.Tensor
import Util.JSON

-- Should the compiler make sure there aren't conflicting nonterminal domains?
-- This is only really a sanity check, and can be turned on/off as pleased
-- (though for the sake of efficiency, perhaps better off for stable releases)
checkDomsEq = True

type Domain = [String] -- list of values for some type
type Factor = (String, Maybe Weights)
type Prob = Double
type Weights = Tensor Prob
type Label = String
--type Nonterminal = (Label, String) -- domain must be a singleton

-- d = type of domain
data Node d = Node {node_label :: Label, node_domain :: d}

toNodes :: [(Label, d)] -> [Node d]
toNodes = map (uncurry Node)
--type Node d = (Label, d) -- (label, domain)
--node = (,)
--node_label = fst
--node_domain = snd

data Edge = Edge { edge_atts :: [Int], edge_label :: Label }
  deriving Eq
data HGF d = HGF { hgf_nodes :: [Node d], hgf_edges :: [Edge], hgf_exts :: [Int]}
  deriving Eq
data Edge' d = Edge' { edge_atts' :: [(Label, d)], edge_label' :: Label }
  deriving Eq
data HGF' d = HGF' { hgf_nodes' :: [(Label, d)], hgf_edges' :: [Edge' d], hgf_exts' :: [(Label, d)] }
  deriving Eq
data Rule d = Rule String (HGF d)
  deriving Eq
data FGG d = FGG {
  domains :: Map String d,                  -- node label to values
  factors :: Map String (d, Maybe Weights), -- edge label to att node labels, weights
  nonterminals :: Map String d,             -- nt name to attachment node labels
  start :: String,                          -- nt name
  rules :: [(Int, Rule Label)]
}

instance Eq (Node d) where
  Node n1 _ == Node n2 _ = n1 == n2
instance Ord (Node d) where
  compare (Node n1 _) (Node n2 _) = compare n1 n2
instance Functor Node where
  fmap f (Node l d) = Node l (f d)
instance Functor HGF where
  fmap f (HGF ns es xs) = HGF [fmap f n | n <- ns] es xs
instance Functor Edge' where
  fmap f (Edge' ns l) = Edge' [fmap f n | n <- ns] l
instance Functor HGF' where
  fmap f (HGF' ns es xs) =
    HGF' [fmap f n | n <- ns] [fmap f e | e <- es] [fmap f x | x <- xs]
instance Functor Rule where
  fmap f (Rule l hgf) = Rule l (fmap f hgf)
instance Functor FGG where
  fmap f (FGG ds fs nts s rs) =
    FGG (fmap f ds)
        (fmap (\ (d, mws) -> (f d, mws)) fs)
        (fmap f nts)
        s
        (fmap (\ (i, r) -> (i, fmap show r)) rs)

-- Convert a HGF' to a HFG
castHGF :: HGF' d -> HGF d
castHGF (HGF' ns es xs) =
  let ns' = nub (toNodes ns)
      m = Map.fromList (zip ns' [0..]) in
    HGF ns'
      [Edge [m Map.! n | n <- toNodes as] l | Edge' as l <- es]
      (nub [m Map.! n | n <- toNodes xs])

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

-- Convert an FGG into a JSON
fgg_to_json :: FGG Domain -> JSON
fgg_to_json (FGG ds fs nts s rs) =
  let mapToList = \ ds f -> JSobject $ Map.toList $ fmap f ds in
  JSobject
    [("grammar", JSobject 
      [("terminals", mapToList fs $
         \ (d, mws) -> JSobject [("type", JSarray $ map JSstring d)]),
       ("nonterminals", mapToList nts $
         \ d -> JSobject [
           ("type", JSarray $ map JSstring d)
         ]),
        ("start", JSstring s),
        ("rules", JSarray $ concat $ flip map (nubBy (\ (_, r1) (_, r2) -> r1 == r2) rs) $
          \ (reps, Rule lhs (HGF ns es xs)) -> replicate reps $ JSobject [
             ("lhs", JSstring lhs),
             ("rhs", JSobject [
                 ("nodes", JSarray [JSobject [("label", JSstring d)] | Node n d <- ns]),
                 ("edges", JSarray $ flip map es $
                   \ (Edge atts l) -> JSobject [
                     ("attachments", JSarray (map JSint atts)),
                     ("label", JSstring l)
                   ]),
                 ("externals", JSarray $ map JSint xs)
               ])
         ])
      ]),
    ("interpretation", JSobject [
      ("domains", mapToList ds $
         \ ds' -> JSobject [
           ("class", JSstring "finite"),
           ("values", JSarray $ map JSstring ds')
         ]),
         ("factors",
          let fs_filtered = Map.mapMaybe (\ (d, mws) -> maybe Nothing (\ ws -> Just (d, ws)) mws) fs in
          mapToList fs_filtered $
           \ (d, ws) -> JSobject [
             ("function", JSstring "finite"),
               ("type", JSarray $ map JSstring d),
               ("weights", weights_to_json ws)
             ])
        ])
    ]


showFGG :: FGG Domain -> String
showFGG = pprint_json . fgg_to_json

-- Default FGG
emptyFGG :: String -> FGG d
emptyFGG s = FGG Map.empty Map.empty Map.empty s []

-- Construct an FGG from a list of rules, a start symbol,
-- and a function that gives the possible values of each type
rulesToFGG :: Show d => (d -> Domain) -> String -> [(Int, Rule d)] -> [(Label, d)] -> [Factor] -> FGG Domain
rulesToFGG dom start rs nts facs =
  FGG ds fs nts' start rsdom
  where
    rs' = nubBy (\ (_, r1) (_, r2) -> r1 == r2) rs
    rs'' = [r | (_, r) <- rs']
    rsdom = [(i, fmap show r) | (i, r) <- rs']
    
    ds  = foldr (\ (Rule lhs (HGF ns es xs)) m ->
                   foldr (\ (Node n d) -> Map.insert (show d) (dom d)) m ns) Map.empty rs''

    domsEq = \ x d1 d2 -> if not checkDomsEq || d1 == d2 then d1 else error
      ("Conflicting domains for nonterminal " ++ x ++ ": " ++
        show d1 ++ " vs " ++ show d2)

    nts'' = fmap dom (Map.fromList nts)

    nts' = foldr (\ (Rule lhs (HGF ns _ xs)) ->
                    Map.insertWith (domsEq lhs) lhs [show (node_domain (ns !! i)) {-node_label (ns !! i)-} | i <- xs]) nts'' rs''

    getFac = \ l lhs -> maybe (error ("In the rule " ++ lhs ++ ", no factor named " ++ l))
                      id $ lookup l facs

    fs  = foldr (\ (Rule lhs (HGF ns es xs)) m ->
                   foldr (\ (Edge atts l) ->
                             if Map.member l nts' then id else
                               Map.insert l ([show (node_domain (ns !! i)) {-node_label (ns !! i)-} | i <- atts], getFac l lhs))
                         m es)
                Map.empty rs''
