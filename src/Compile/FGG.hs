{- FGG datatype code -}

module FGG.FGG where
import qualified Data.Map as Map
import Data.List
import Util.Helpers
import Exprs
import Util.Tensor
import Util.JSON
import Show()

-- Should the compiler make sure there aren't conflicting nonterminal domains?
-- This is only really a sanity check, and can be turned on/off as pleased
-- (though for the sake of efficiency, perhaps better off for stable releases)
checkDomsEq = True

type Nonterminal = (Var, Type)
type Domain = [String] -- list of values for some type
type Value = String
type FType = [Value]
type Factor = (String, Maybe Weights)
type Prob = Double
type Weights = Tensor Prob
data Edge = Edge { edge_atts :: [Int], edge_label :: String }
  deriving Eq
data Edge' = Edge' { edge_atts' :: [(Var, Type)], edge_label' :: String }
  deriving Eq
data HGF = HGF { hgf_nodes :: [Type], hgf_edges :: [Edge], hgf_exts :: [Int]}
  deriving Eq
data HGF' = HGF' { hgf_nodes' :: [(Var, Type)], hgf_edges' :: [Edge'], hgf_exts' :: [(Var, Type)] }
  deriving Eq
data Rule = Rule String HGF
  deriving Eq
data FGG_JSON = FGG_JSON {
  domains :: Map String FType,
  factors :: Map String (Domain, Maybe Weights),
  nonterminals :: Map String Domain,
  start :: String,
  rules :: [(Int, Rule)]
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

-- Convert an FGG into a JSON
fgg_to_json :: FGG_JSON -> JSON
fgg_to_json (FGG_JSON ds fs nts s rs) =
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
        ("rules", JSarray $ concat $ flip map (nub rs) $
          \ (reps, Rule lhs (HGF ns es xs)) -> replicate reps $ JSobject [
             ("lhs", JSstring lhs),
             ("rhs", JSobject [
                 ("nodes", JSarray [JSobject [("label", JSstring (show n))] | n <- ns]),
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
             ("function", JSstring "categorical"),
               ("type", JSarray $ map JSstring d),
               ("weights", weights_to_json ws)
             ])
        ])
    ]

instance Show FGG_JSON where
  show = pprint_json . fgg_to_json

-- Default FGG
emptyFGG :: String -> FGG_JSON
emptyFGG s = FGG_JSON Map.empty Map.empty Map.empty s []

-- Construct an FGG from a list of rules, a start symbol,
-- and a function that gives the possible values of each type
rulesToFGG :: (Type -> [String]) -> String -> [(Int, Rule)] -> [Nonterminal] -> [Factor] -> FGG_JSON
rulesToFGG doms start rs nts facs =
  let rs' = nubBy (\ (_, r1) (_, r2) -> r1 == r2) rs
      rs'' = [r | (_, r) <- rs']
      ds  = foldr (\ (Rule lhs (HGF ns es xs)) m ->
                     foldr (\ n -> Map.insert (show n) (doms n)) m ns) Map.empty rs''
      domsEq = \ x d1 d2 -> if not checkDomsEq || d1 == d2 then d1 else error
        ("Conflicting domains for nonterminal " ++ x ++ ": " ++
          show d1 ++ " vs " ++ show d2)
      nts'' = foldr (\ (x, tp) -> Map.insert x [show tp]) Map.empty nts
      nts' = foldr (\ (Rule lhs (HGF ns _ xs)) ->
                      Map.insertWith (domsEq lhs) lhs [show (ns !! i) | i <- xs]) nts'' rs''
      getFac = \ l lhs -> maybe (error ("In the rule " ++ lhs ++ ", no factor named " ++ l))
                        id $ lookup l facs
      fs  = foldr (\ (Rule lhs (HGF ns es xs)) m ->
                     foldr (\ (Edge atts l) ->
                               if Map.member l nts' then id else
                                 Map.insert l ([show (ns !! i) | i <- atts], getFac l lhs))
                           m es)
                  Map.empty rs''
  in
    FGG_JSON ds fs nts' start rs'
