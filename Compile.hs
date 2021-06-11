module Compile where
import Data.List
import Exprs
import FGG
import Util
import RuleM

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
  -- +> maybe returnRule (addFactor fac) (getTypeWeights tp)


-- Bind a list of external nodes, and add rules for them
bindExts :: Bool -> [(Var, Type)] -> RuleM -> RuleM
bindExts addVarRules xs' (RuleM rs xs fs) =
  let keep = not . flip elem (map fst xs') . fst in
  foldr (\ (x, tp) r -> var2fgg x tp +> r) (RuleM rs (filter keep xs) fs) xs'

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

ctorEtaRule :: Ctor -> Var -> RuleM
ctorEtaRule (Ctor x as) y =
  let eta = (ctorAddLams x (ctorGetArgs x as) (TpVar y)) in
  addRule' x [TpVar y] [Edge [0] (show eta)] [0]

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

-- Add a rule for this particular case in a case-of statement
case2fgg :: [(Var, Type)] -> Term -> Case -> RuleM
case2fgg xs_ctm (TmCase ctm cs y tp) (Case x as xtm) =
  bindExts True as (term2fgg xtm) +>= \ xs_xtm ->
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
  foldr (\ c r -> case2fgg xs (TmCase tm cs y tp) c +> r) returnRule cs
term2fgg (TmSamp d y) =
  addFactor (show $ TmSamp d y) (ThisWeight (WeightsData 1)) +> -- TODO
  returnRule -- TODO

-- Goes through a program and adds all the rules for it
prog2fgg :: Progs -> (RuleM, [(Var, Domain)])
prog2fgg (ProgExec tm) = (term2fgg tm, [])
prog2fgg (ProgFun x tp tm ps) =
  let (rm, ds) = prog2fgg ps in
    ((rm +> term2fgg tm +> addRule' x [tp] [Edge [0] (show tm)] [0]), ds)
prog2fgg (ProgData y cs ps) =
  let (rm, ds) = prog2fgg ps in
  ((rm +> addFactor (typeFactorName (TpVar y)) (getCtorEqWeights (length cs)) +>
      foldr (\ c r -> r +> ctorRules c y cs) returnRule cs),
   ((y, map (\ (Ctor x tps) -> show (ctorAddArgs x (ctorGetArgs x tps) (TpVar y))) cs) : ds))

-- TODO: Add values for arrow-type domains (e.g. Bool -> Maybe)

-- Converts an elaborated program into an FGG
file2fgg :: Progs -> FGG_JSON
file2fgg ps =
  let (RuleM rs xs fs, ds) = prog2fgg ps in
    rulesToFGG (\ y -> maybe [] id (lookup y ds)) (show $ getStartTerm ps) (reverse rs) fs
