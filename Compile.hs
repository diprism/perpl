module Compile where
import Data.List
import Exprs
import FGG
import Check
import Util

-- RuleM monad-like datatype and funcions
type External = (Var, Type)
data RuleM = RuleM [Rule] [External]

-- RuleM instances of >>= and >= (since not
-- technically a monad, need to pick new names)
infixl 1 +>=, +>
(+>=) :: RuleM -> ([External] -> RuleM) -> RuleM
RuleM rs xs +>= f = let RuleM rs' xs' = f xs in RuleM (rs ++ rs') (xs ++ xs')

(+>) :: RuleM -> RuleM -> RuleM
r1 +> r2 = r1 +>= \ _ -> r2

-- Add a list of external nodes
addExts :: [(Var, Type)] -> RuleM
addExts xs = RuleM [] xs

-- Add a single external node
addExt :: Var -> Type -> RuleM
addExt x tp = addExts [(x, tp)]

-- Add a list of rules
addRules :: [Rule] -> RuleM
addRules rs = RuleM rs []

-- Add a single rule
addRule :: Rule -> RuleM
addRule r = addRules [r]

-- Add a rule from the given components
addRule' :: String -> [Type] -> [Edge] -> [Int] -> RuleM
addRule' lhs ns es xs = addRule $ Rule lhs $ HGF (map show ns) es xs

-- Do nothing new
returnRule :: RuleM
returnRule = RuleM [] []

-- Naming convention for factor v=(v1,v2)
pairFactorName :: Type -> Type -> String
pairFactorName tp1 tp2 = "v=(" ++ show tp1 ++ "," ++ show tp2 ++ ")"

-- Naming convention for constructor factor
ctorFactorName :: Var -> String
ctorFactorName c = "v=" ++ c


-- Local var rule
var2fgg :: Var -> Type -> RuleM
var2fgg x tp =
  addRule' x [tp, tp] [Edge [0, 1] ("=" ++ show tp)] [0, 1]

-- Extract rules from a RuleM
getRules :: RuleM -> [Rule]
getRules (RuleM rs xs) = rs

-- Bind a list of external nodes, and add rules for them
bindExts :: [(Var, Type)] -> RuleM -> RuleM
bindExts xs' (RuleM rs xs) =
  let keep = flip elem (map fst xs') . fst in
  foldr (\ (x, tp) r -> var2fgg x tp +> r) (RuleM rs (filter keep xs)) xs'

-- Bind an external node, and add a rule for it
bindExt :: Var -> Type -> RuleM -> RuleM
bindExt x tp = bindExts [(x, tp)]

-- Add rule for a term application
tmapp2fgg :: Term -> RuleM
tmapp2fgg (TmApp tm1 tm2 tp2 tp) =
  term2fgg tm1 +>= \ xs1 ->
  term2fgg tm2 +>= \ xs2 ->
  let (ns, [[itp2, itp, iarr], ixs1, ixs2]) =
        combine [[tp2, tp, TpArr tp2 tp], map snd xs1, map snd xs2]
      es = [Edge (itp2 : ixs2) (show tm2),
            Edge (iarr : ixs1) (show tm1),
            Edge [itp2, itp, iarr] (pairFactorName tp2 tp)]
      xs = itp : ixs1 ++ ixs2 in
    addRule' (show (TmApp tm1 tm2 tp2 tp)) ns es xs

-- Split up x a0 a1 a2 ... into [(a0, ?), (a1, ?), (a2, ?), ...]
getCtorArgs :: Term -> [(Var, Type)]
getCtorArgs (TmVar x tp sc) = []
getCtorArgs (TmApp tm (TmVar x tp ScopeLocal) _ _) = (x, tp) : getCtorArgs tm

-- Add rule for a constructor
ctor2fgg :: Ctor -> Var -> RuleM
ctor2fgg (Ctor x as) y =
  let as' = map (ctorEtaName x) [0..length as - 1]
      (ns, [ias1, ias2, [iy]]) = combine [as, as, [TpVar y]]
      ias = zip3 ias1 ias2 as'
      es_as = map (\ (ia1, ia2, a) -> Edge [ia1, ia2] a) ias
      es = Edge (iy : ias2) (ctorFactorName x) : es_as
      xs = iy : ias1 in
    addRule' x ns es xs

-- Add a rule for this particular case in a case-of statement
case2fgg :: [(Var, Type)] -> Term -> Case -> RuleM
case2fgg xs_ctm (TmCase ctm cs y tp) (Case x as xtm) =
  bindExts as (term2fgg xtm) +>= \ xs_xtm ->
  --let ix = foldr (\ (Case x' _ _) next ix -> if x == x' then ix + 1 else next (ix + 1)) id cs 0 in
  let (ns, [[ictm, ixtm], ixs_as, ixs_ctm, ixs_xtm]) =
        combine [[TpVar y, tp], map snd as, map snd xs_ctm, map snd xs_xtm]
      es = [Edge (ictm : ixs_ctm) (show ctm),
            Edge (ixtm : ixs_xtm ++ ixs_as) (show xtm),
            Edge (ictm : ixs_as) (ctorFactorName x)]
      xs = ixtm : ixs_ctm ++ ixs_xtm in
    addRule' (show (TmCase ctm cs y tp)) ns es xs
case2fgg xs _ (Case x as xtm) =
  error "case2fgg expected a TmCase, but got something else"

-- Traverse a term and add all rules for subexpressions
term2fgg :: Term -> RuleM
term2fgg (TmCtor x as) =
  addExts as
term2fgg (TmVar x tp local) =
  case local of
    ScopeGlobal -> returnRule
    ScopeLocal -> addExt x tp
    ScopeCtor -> error "term2fgg should not see a TmVar with ScopeCtor" --term2fgg (ctorEtaExpand x tp)
term2fgg (TmLam x tp tm tp') =
  bindExt x tp (term2fgg tm) +>= \ xs' ->
  let (ns, [[itp, itp', iarr], ixs']) = combine [[tp, tp', TpArr tp tp'], map snd xs']
      es = [Edge ([itp, itp'] ++ ixs') (show tm),
            Edge [itp, itp', iarr] (pairFactorName tp tp')]
      xs = iarr : ixs' in
    addRule' (show (TmLam x tp tm tp')) ns es xs
term2fgg (TmApp tm1 tm2 tp2 tp) =
  tmapp2fgg (TmApp tm1 tm2 tp2 tp)
--  case splitApps (TmApp tm1 tm2 tp2 tp) of
--    (((TmVar x xtp ScopeCtor), TpVar y), as) -> ctor2fgg x xtp y as
--    _ -> tmapp2fgg (TmApp tm1 tm2 tp2 tp)
term2fgg (TmCase tm cs y tp) =
  term2fgg tm +>= \ xs ->
  foldr (\ c r -> case2fgg xs (TmCase tm cs y tp) c +> r) returnRule cs
term2fgg (TmSamp d y) =
  returnRule -- TODO

-- Extracts the start term at the end of a program
getStartTerm :: Progs -> Term
getStartTerm (ProgExec tm) = tm
getStartTerm (ProgFun x tp tm ps) = getStartTerm ps
getStartTerm (ProgData y cs ps) = getStartTerm ps

-- Goes through a program and adds all the rules for it
prog2fgg :: Progs -> RuleM
prog2fgg (ProgExec tm) = term2fgg tm
prog2fgg (ProgFun x tp tm ps) =
  prog2fgg ps +> term2fgg tm +>
  addRule' x [last $ splitArrows tp] [Edge [0] (show tm)] [0]
prog2fgg (ProgData y cs ps) =
  prog2fgg ps +>
  foldr (\ c r -> r +> ctor2fgg c y) returnRule cs

-- Converts an elaborated program into an FGG
file2fgg :: Progs -> FGG_JSON
file2fgg ps = rulesToFGG (\ y -> []) (show $ getStartTerm ps) (reverse $ getRules $ prog2fgg ps)
