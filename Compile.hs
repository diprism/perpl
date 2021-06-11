module Compile where
import Data.List
import Exprs
import FGG
import Check
import Util

-- RuleM monad-like datatype and funcions
type External = (Var, Type)
data RuleM = RuleM [Rule] [External] [Factor]

-- RuleM instances of >>= and >= (since not
-- technically a monad, need to pick new names)
infixl 1 +>=, +>
(+>=) :: RuleM -> ([External] -> RuleM) -> RuleM
RuleM rs xs fs +>= g =
  let RuleM rs' xs' fs' = g xs in
    RuleM (rs ++ rs') (xs ++ xs') (concatFactors fs fs')

(+>) :: RuleM -> RuleM -> RuleM
r1 +> r2 = r1 +>= \ _ -> r2

-- Add a list of external nodes
addExts :: [(Var, Type)] -> RuleM
addExts xs = RuleM [] xs []

-- Add a single external node
addExt :: Var -> Type -> RuleM
addExt x tp = addExts [(x, tp)]

-- Add a list of rules
addRules :: [Rule] -> RuleM
addRules rs = RuleM rs [] []

-- Add a single rule
addRule :: Rule -> RuleM
addRule r = addRules [r]

-- Add a rule from the given components
addRule' :: String -> [Type] -> [Edge] -> [Int] -> RuleM
addRule' lhs ns es xs = addRule $ Rule lhs $ HGF (map show ns) es xs

addFactor :: Var -> PreWeight -> RuleM
addFactor x w = RuleM [] [] [(x, w)]

-- Do nothing new
returnRule :: RuleM
returnRule = RuleM [] [] []

-- Naming convention for testing equality two terms of the same type
typeFactorName :: Type -> String
typeFactorName tp = "==" ++ show tp

-- Naming convention for factor v=(v1,v2)
pairFactorName :: Type -> Type -> String
pairFactorName tp1 tp2 = "v=(" ++ show tp1 ++ "," ++ show tp2 ++ ")"

-- Naming convention for constructor factor
ctorFactorName :: Var -> [(Var, Type)] -> String
ctorFactorName x as = "v=" ++ show (TmCtor x as)


-- Local var rule
var2fgg :: Var -> Type -> RuleM
var2fgg x tp =
  let fac = typeFactorName tp in
  addRule' x [tp, tp] [Edge [0, 1] fac] [0, 1]
  -- +> maybe returnRule (addFactor fac) (getTypeWeights tp)

-- Extract rules from a RuleM
getRules :: RuleM -> [Rule]
getRules (RuleM rs xs fs) = rs

-- Bind a list of external nodes, and add rules for them
bindExts :: [(Var, Type)] -> RuleM -> RuleM
bindExts xs' (RuleM rs xs fs) =
  let keep = not . flip elem (map fst xs') . fst in
  --foldr (\ (x, tp) r -> var2fgg x tp +> r) (RuleM rs (filter keep xs) fs) xs'
    RuleM rs (filter keep xs) fs

-- Bind an external node, and add a rule for it
bindExt :: Var -> Type -> RuleM -> RuleM
bindExt x tp = bindExts [(x, tp)]

getPairWeights :: Type -> Type -> PreWeight
getPairWeights tp1 tp2 = PairWeight ((show tp1), (show tp2))

getCtorWeights :: Int {- ctor index -} -> Int {- num of ctors -} -> PreWeight
getCtorWeights ci cs = ThisWeight $ WeightsDims $ WeightsData $ weightsRow ci cs

-- Identity matrix
getCtorEqWeights :: Int {- num of ctors -} -> PreWeight
getCtorEqWeights cs =
  let is = [0..cs - 1] in
    ThisWeight $ fmap (\ (i, j) -> if i == j then 1 else 0) $
      WeightsDims $ WeightsDims $ WeightsData $ kronecker is is

-- Add rule for a term application
tmapp2fgg :: Term -> RuleM
tmapp2fgg (TmApp tm1 tm2 tp2 tp) =
  term2fgg tm1 +>= \ xs1 ->
  term2fgg tm2 +>= \ xs2 ->
  let fac = pairFactorName tp2 tp
      (ns, [[itp2, itp, iarr], ixs1, ixs2]) =
        combine [[tp2, tp, TpArr tp2 tp], map snd xs1, map snd xs2]
      es = [Edge (itp2 : ixs2) (show tm2),
            Edge (iarr : ixs1) (show tm1),
            Edge [itp2, itp, iarr] fac]
      xs = itp : ixs1 ++ ixs2 in
    addRule' (show (TmApp tm1 tm2 tp2 tp)) ns es xs +>
    addFactor fac (getPairWeights tp2 tp)

-- Split up x a0 a1 a2 ... into [(a0, ?), (a1, ?), (a2, ?), ...]
getCtorArgs :: Term -> [(Var, Type)]
getCtorArgs (TmVar x tp sc) = []
getCtorArgs (TmApp tm (TmVar x tp ScopeLocal) _ _) = (x, tp) : getCtorArgs tm

-- Add rule for a constructor
ctor2fgg :: Ctor -> Var -> [Ctor] -> RuleM
ctor2fgg (Ctor x as) y cs =
  let ix = foldr (\ (Ctor x' _) next ix -> if x == x' then ix else next (ix + 1)) id cs 0
      as' = map (ctorEtaName x) [0..length as - 1]
      (ns, [ias, [iy]]) = combine [as, [TpVar y]]
      ias' = zip ias as'
      --es_as = map (\ (ia1, ia2, a) -> Edge [ia1, ia2] a) ias
      tm = TmCtor x (zip as' as)
      fac = ctorFactorName x (zip as' as)
      es = [Edge (ias ++ [iy]) fac]
      xs = ias ++ [iy] in
    addRule' (show tm) ns es xs +>
    addFactor fac (getCtorWeights ix (length cs))

{-ctor2fgg :: Ctor -> Var -> [Ctor] -> RuleM
ctor2fgg (Ctor x as) y cs =
  let ix = foldr (\ (Ctor x' _) next ix -> if x == x' then ix else next (ix + 1)) id cs 0
      as' = map (ctorEtaName x) [0..length as - 1]
      (ns, [ias1, ias2, [iy]]) = combine [as, as, [TpVar y]]
      ias = zip3 ias1 ias2 as'
      es_as = map (\ (ia1, ia2, a) -> Edge [ia1, ia2] a) ias
      tm = TmCtor x (zip as' as)
      fac = ctorFactorName x (zip as' as)
      es = Edge (iy : ias2) fac : es_as
      xs = iy : ias1 in
    addRule' (show tm) ns es xs +>
    addFactor fac (getCtorWeights ix (length cs))-}

-- Add a rule for this particular case in a case-of statement
case2fgg :: [(Var, Type)] -> Term -> Case -> RuleM
case2fgg xs_ctm (TmCase ctm cs y tp) (Case x as xtm) =
  bindExts as (term2fgg xtm) +>= \ xs_xtm ->
  let fac = ctorFactorName x (ctorGetArgs x (map snd as))
      (ns, [[ictm, ixtm], ixs_as, ixs_ctm, ixs_xtm]) =
        combine [[TpVar y, tp], map snd as, map snd xs_ctm, map snd xs_xtm]
      es = [Edge (ictm : ixs_ctm) (show ctm),
            Edge (ixtm : ixs_xtm ++ ixs_as) (show xtm),
            Edge (ixs_as ++ [ictm]) fac]
      xs = ixtm : ixs_ctm ++ ixs_xtm in
    addRule' (show (TmCase ctm cs y tp)) ns es xs
case2fgg xs _ (Case x as xtm) =
  error "case2fgg expected a TmCase, but got something else"

-- Traverse a term and add all rules for subexpressions
term2fgg :: Term -> RuleM
term2fgg (TmCtor x as) =
  addExts (reverse as)
term2fgg (TmVar x tp local) =
  case local of
    ScopeGlobal -> returnRule
    ScopeLocal -> addExt x tp
    ScopeCtor -> error "term2fgg should not see a TmVar with ScopeCtor" --term2fgg (ctorEtaExpand x tp)
term2fgg (TmLam x tp tm tp') =
  var2fgg x tp +>
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
  addFactor (show $ TmSamp d y) (ThisWeight (WeightsData 1)) +> -- TODO
  returnRule -- TODO

-- Extracts the start term at the end of a program
getStartTerm :: Progs -> Term
getStartTerm (ProgExec tm) = tm
getStartTerm (ProgFun x tp tm ps) = getStartTerm ps
getStartTerm (ProgData y cs ps) = getStartTerm ps

-- Goes through a program and adds all the rules for it
prog2fgg :: Progs -> (RuleM, [(Var, Domain)])
prog2fgg (ProgExec tm) = (term2fgg tm, [])
prog2fgg (ProgFun x tp tm ps) =
  let (rm, ds) = prog2fgg ps in
    ((rm +> term2fgg tm +> addRule' x [tp] [Edge [0] (show tm)] [0]), ds)
prog2fgg (ProgData y cs ps) =
  let (rm, ds) = prog2fgg ps in
  ((rm +> addFactor (typeFactorName (TpVar y)) (getCtorEqWeights (length cs)) +>
      foldr (\ c r -> r +> ctor2fgg c y cs) returnRule cs),
   ((y, map (\ (Ctor x tps) -> show (TmCtor x (ctorGetArgs x tps)) {- TODO: does this hack really work? -}) cs) : ds))

-- TODO: Add values for arrow-type domains (e.g. Bool -> Maybe)

-- Converts an elaborated program into an FGG
file2fgg :: Progs -> FGG_JSON
file2fgg ps =
  let (RuleM rs xs fs, ds) = prog2fgg ps in
    rulesToFGG (\ y -> maybe [] id (lookup y ds)) (show $ getStartTerm ps) (reverse rs) fs
