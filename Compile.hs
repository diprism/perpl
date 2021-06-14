module Compile where
import Data.List
import Exprs
import FGG
import Util
import RuleM
import Ctxt

-- Naming convention for testing equality two terms of the same type
typeFactorName :: Type -> String
typeFactorName tp = "==" ++ show tp

-- Naming convention for factor v=(v1,v2)
pairFactorName :: Type -> Type -> String
pairFactorName tp1 tp2 = "v=(" ++ show tp1 ++ "," ++ show tp2 ++ ")"

-- Naming convention for constructor factor
ctorFactorName :: Var -> [(Var, Type)] -> String
ctorFactorName x as = "v=" ++ show (ctorAddArgs x as (TpVar "irrelevant"))

-- Establishes naming convention for eta-expanding a constructor.
-- So Cons h t -> (\ 0Cons. \ 1Cons. Cons 0Cons 1Cons) h t.
-- This is necessary so that the FGG can use one rule for each
-- constructor, and not for each usage of it in the code.
-- It also fixes the issue of partially-applied constructors.
ctorEtaName :: Var -> Int -> Var
ctorEtaName x i = show i ++ x

-- Returns the names of the args for a constructor
ctorGetArgs :: Var -> [Type] -> [(Var, Type)]
ctorGetArgs x tps =
  zip (map (ctorEtaName x) [0..length tps - 1]) tps

-- Turns a constructor into one with all its args applied
ctorAddArgs :: Var -> [(Var, Type)] -> Type -> Term
ctorAddArgs x as tp = h as tp
  where
    h [] tp = TmVar x tp ScopeCtor
    h ((a, atp) : as) tp =
      let tm = h as (TpArr atp tp) in
        TmApp tm (TmVar a atp ScopeLocal) atp tp

-- Eta-expands a constructor
ctorAddLams :: Var -> [(Var, Type)] -> Type -> Term
ctorAddLams x as tp =
  foldr (\ (a, atp) tm -> TmLam a atp tm (getType tm))
    (ctorAddArgs x as tp) as

-- Converts Cons -> (\ 0Cons. \ 1Cons. Cons 0Cons 1Cons)
ctorEtaExpand :: Var -> Type -> Term
ctorEtaExpand x = uncurry (ctorAddLams x . ctorGetArgs x) . splitArrows


-- Local var rule
var2fgg :: Var -> Type -> RuleM
var2fgg x tp =
  let fac = typeFactorName tp in
  addRule' x [tp, tp] [Edge [0, 1] fac] [0, 1]


-- Bind a list of external nodes, and add rules for them
bindExts :: Bool -> [(Var, Type)] -> RuleM -> RuleM
bindExts addVarRules xs' (RuleM rs xs fs) =
  let keep = not . flip elem (map fst xs') . fst
      rm = RuleM rs (filter keep xs) fs in
    if addVarRules
      then foldr (\ (x, tp) r -> var2fgg x tp +> r) rm xs'
      else rm

-- Bind an external node, and add a rule for it
bindExt :: Bool -> Var -> Type -> RuleM -> RuleM
bindExt addVarRule x tp = bindExts addVarRule [(x, tp)]

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

-- Eta-expands a constructor and adds all necessary rules
ctorEtaRule :: Ctor -> Var -> RuleM
ctorEtaRule (Ctor x as) y =
  let eta = (ctorAddLams x (ctorGetArgs x as) (TpVar y)) in
  addRule' x [TpVar y] [Edge [0] (show eta)] [0]

-- Adds the lambda rules for an eta-expanded constructor
ctorLamRules :: Ctor -> Var -> RuleM
ctorLamRules (Ctor x as) y = fst $ h as' where
  as' = ctorGetArgs x as
  h [] = (returnRule, ctorAddArgs x as' (TpVar y))
  h ((a, tp) : as) =
    let (rm, tm) = h as
        tp' = joinArrows (map snd as) (TpVar y) in
      (lamRule False a tp tm tp' rm, TmLam a tp tm tp')

-- Add rule for a constructor
ctorRules :: Ctor -> Var -> [Ctor] -> RuleM
ctorRules (Ctor x as) y cs =
  let ix = foldr (\ (Ctor x' _) next ix -> if x == x' then ix else next (ix + 1)) id cs 0
      as' = map (ctorEtaName x) [0..length as - 1]
      (ns, [ias, [iy]]) = combine [as, [TpVar y]]
      ias' = zip ias as'
      tm = ctorAddArgs x (zip as' as) (TpVar y)
      fac = ctorFactorName x (zip as' as)
      es = [Edge (ias ++ [iy]) fac]
      xs = ias ++ [iy] in
    addRule' (show tm) ns es xs +>
    ctorEtaRule  (Ctor x as) y +>
    ctorLamRules (Ctor x as) y +>
    addFactor fac (getCtorWeights ix (length cs))

ctorsRules :: [Ctor] -> Var -> RuleM
ctorsRules cs y = foldr (\ c r -> r +> ctorRules c y cs) returnRule cs

ctorsFactors :: [Ctor] -> Var -> RuleM
ctorsFactors cs y = addFactor (typeFactorName (TpVar y)) (getCtorEqWeights (length cs))

-- Add a rule for this particular case in a case-of statement
caseRule :: [(Var, Type)] -> Term -> Case -> RuleM
caseRule xs_ctm (TmCase ctm cs y tp) (Case x as xtm) =
  bindExts True as (term2fgg xtm) +>= \ xs_xtm ->
  let fac = ctorFactorName x (ctorGetArgs x (map snd as))
      (ns, [[ictm, ixtm], ixs_as, ixs_ctm, ixs_xtm]) =
        combine [[TpVar y, tp], map snd as, map snd xs_ctm, map snd xs_xtm]
      es = [Edge (ictm : ixs_ctm) (show ctm),
            Edge (ixtm : ixs_xtm ++ ixs_as) (show xtm),
            Edge (ixs_as ++ [ictm]) fac]
      xs = ixtm : ixs_ctm ++ ixs_xtm in
    addRule' (show (TmCase ctm cs y tp)) ns es xs
caseRule xs _ (Case x as xtm) =
  error "caseRule expected a TmCase, but got something else"

-- Add a rule for a lambda term
lamRule :: Bool -> Var -> Type -> Term -> Type -> RuleM -> RuleM
lamRule addVarRule x tp tm tp' rm =
  bindExt addVarRule x tp rm +>= \ xs' ->
  let (ns, [[itp, itp', iarr], ixs']) = combine [[tp, tp', TpArr tp tp'], map snd xs']
      es = [Edge ([itp, itp'] ++ ixs') (show tm),
            Edge [itp, itp', iarr] (pairFactorName tp tp')]
      xs = iarr : ixs' in
    addRule' (show (TmLam x tp tm tp')) ns es xs

-- Traverse a term and add all rules for subexpressions
term2fgg :: Term -> RuleM
term2fgg (TmVar x tp local) =
  case local of
    ScopeGlobal -> returnRule
    ScopeLocal -> addExt x tp
    ScopeCtor -> returnRule
term2fgg (TmLam x tp tm tp') =
  lamRule True x tp tm tp' (term2fgg tm)
term2fgg (TmApp tm1 tm2 tp2 tp) =
  tmapp2fgg (TmApp tm1 tm2 tp2 tp)
term2fgg (TmCase tm cs y tp) =
  term2fgg tm +>= \ xs ->
  foldr (\ c r -> caseRule xs (TmCase tm cs y tp) c +> r) returnRule cs
term2fgg (TmSamp d y) =
  addFactor (show $ TmSamp d y) (ThisWeight (WeightsData 1)) +> -- TODO
  returnRule -- TODO

-- Goes through a program and adds all the rules for it
prog2fgg :: Progs -> RuleM
prog2fgg (ProgExec tm) = term2fgg tm
prog2fgg (ProgFun x tp tm ps) =
  prog2fgg ps +> term2fgg tm +> addRule' x [tp] [Edge [0] (show tm)] [0]
prog2fgg (ProgData y cs ps) =
  prog2fgg ps +> ctorsFactors cs y +> ctorsRules cs y

-- TODO: Add values for arrow-type domains (e.g. Bool -> Maybe)
-- (Will likely require some ordering of which to add first, so
-- that Bool -> Maybe is already there for Int -> Bool -> Maybe)

-- TODO: External node ordering (that is, make sure v, v1, v2,
-- etc... are connected correctly)

getDomain :: Ctxt -> Type -> [String]
getDomain g (TpVar y) = maybe2 (ctxtLookupType g y) [] $ map $ \ (Ctor x as) -> show $ ctorAddArgs x (ctorGetArgs x as) (TpVar y)
getDomain g (TpArr tp1 tp2) = map (\ (s1, s2) -> "(" ++ s1 ++ "," ++ s2 ++ ")") (concat (kronecker (getDomain g tp1) (getDomain g tp2)))

-- Converts an elaborated program into an FGG
file2fgg :: Ctxt -> Progs -> FGG_JSON
file2fgg g ps =
  let RuleM rs xs fs = prog2fgg ps in
    rulesToFGG (getDomain g) (show $ getStartTerm ps) (reverse rs) fs
