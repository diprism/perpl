module Compile where
import Data.List
import Exprs
import FGG
import Util
import RuleM
import Ctxt
import Free

-- TODO: Figure out how to handle externals for terms like
--         case q of false -> q | true -> true
--       (where some var occurs multiple times)

-- Local var rule
var2fgg :: Var -> Type -> RuleM
var2fgg x tp =
  let fac = typeFactorName tp in
  addRule' (TmVar x tp ScopeLocal) [tp, tp] [Edge [0, 1] fac] [0, 1]

-- Bind a list of external nodes, and add rules for them
bindExts :: Bool -> [(Var, Type)] -> RuleM -> RuleM
bindExts addVarRules xs' (RuleM rs xs nts fs) =
  let keep = not . flip elem (map fst xs') . fst
      rm = RuleM rs (filter keep xs) nts fs in
    if addVarRules
      then foldr (\ (x, tp) r -> var2fgg x tp +> r) rm xs'
      else rm

-- Bind an external node, and add a rule for it
bindExt :: Bool -> Var -> Type -> RuleM -> RuleM
bindExt addVarRule x tp = bindExts addVarRule [(x, tp)]

-- Only takes the external nodes from one of the cases,
-- because they should all have the same externals and
-- we don't want to include them more than once.
bindCases :: [RuleM] -> RuleM
bindCases =
  foldr (\ rm rm' -> rm +> resetExts rm') returnRule


-- Add rule for a term application
tmapp2fgg :: Ctxt -> Term -> RuleM
tmapp2fgg g (TmApp tm1 tm2 tp2 tp) =
  term2fgg g tm1 +>= \ xs1 ->
  term2fgg g tm2 +>= \ xs2 ->
  let fac = pairFactorName tp2 tp
      (ns, [[itp2, itp, iarr], ixs1, ixs2]) =
        combine [[tp2, tp, TpArr tp2 tp], map snd xs1, map snd xs2]
      es = [Edge (ixs2 ++ [itp2]) (show tm2),
            Edge (ixs1 ++ [iarr]) (show tm1),
            Edge [itp2, itp, iarr] fac]
      xs = ixs1 ++ ixs2 ++ [itp] in
    addRule' (TmApp tm1 tm2 tp2 tp) ns es xs +>
    addFactor fac (getPairWeights tp2 tp)

-- Add rule for a constructor
ctorRules :: Ctxt -> Ctor -> Type -> [Ctor] -> RuleM
ctorRules g (Ctor x as) y cs =
  let ix = foldr (\ (Ctor x' _) next ix -> if x == x' then ix else next (ix + 1)) id cs 0
      as' = map (ctorEtaName x) [0..length as - 1]
      (ns, [ias, [iy]]) = combine [as, [y]]
      ias' = zip ias as'
      fac = ctorFactorName x (toTermArgs (zip as' as)) y
      es = [Edge (ias ++ [iy]) fac]
      xs = ias ++ [iy]
      tm = TmCtor x (map (\ (a, atp) -> (TmVar a atp ScopeLocal, atp)) (zip as' as)) y in
    addRule' tm ns es xs +>
    addFactor (ctorFactorNameDefault x as y)
      (getCtorWeightsFlat (domainValues g) (Ctor x as) cs)

ctorsRules :: Ctxt -> [Ctor] -> Type -> RuleM
ctorsRules g cs y =
  foldr (\ (fac, ws) rm -> addFactor fac ws +> rm) returnRule
    (getCtorWeightsAll (domainValues g) cs y) +>
  foldr (\ (Ctor x as) r -> r +> ctorRules g (Ctor x as) y cs) returnRule cs +>
  addFactor (typeFactorName y) (getCtorEqWeights (domainSize g y))

-- Add a rule for this particular case in a case-of statement
caseRule :: Ctxt -> [(Var, Type)] -> Term -> Case -> RuleM
caseRule g xs_ctm (TmCase ctm y cs tp) (Case x as xtm) =
  --(\ _ -> error (show (Case x as xtm) ++ ", " ++ show tp)) $
  let g' = ctxtDeclArgs g as in
  bindExts True as (term2fgg g' xtm) +>= \ xs_xtm ->
  let fac = ctorFactorName x (toTermArgs (ctorGetArgs x (map snd as))) y
      (ns, [[ictm, ixtm], ixs_as, ixs_ctm, ixs_xtm]) =
        combine [[y, tp], map snd as, map snd xs_ctm, map snd xs_xtm]
      es = [Edge (ixs_ctm ++ [ictm]) (show ctm),
            Edge (ixs_xtm ++ ixs_as ++ [ixtm]) (show xtm),
            Edge (ixs_as ++ [ictm]) fac]
      xs = ixs_ctm ++ ixs_xtm ++ [ixtm] in
    addRule' (TmCase ctm y cs tp) ns es xs
caseRule g xs _ (Case x as xtm) =
  error "caseRule expected a TmCase, but got something else"

-- Add a rule for a lambda term
lamRule :: Bool -> Var -> Type -> Term -> Type -> RuleM -> RuleM
lamRule addVarRule x tp tm tp' rm =
  bindExt addVarRule x tp rm +>= \ xs' ->
  let (ns, [[itp, itp', iarr], ixs']) = combine [[tp, tp', TpArr tp tp'], map snd xs']
      es = [Edge (ixs' ++ [itp, itp']) (show tm),
            Edge [itp, itp', iarr] (pairFactorName tp tp')]
      xs = ixs' ++ [iarr] in
    addRule' (TmLam x tp tm tp') ns es xs +>
    addFactor (pairFactorName tp tp') (getPairWeights tp tp')

-- Traverse a term and add all rules for subexpressions
term2fgg :: Ctxt -> Term -> RuleM
term2fgg g (TmVar x tp local) =
  addFactor (typeFactorName tp) (getCtorEqWeights (domainSize g tp)) +>
  case local of
    ScopeGlobal -> returnRule
    ScopeLocal -> addExt x tp
    ScopeCtor -> error ("term2fgg should not see a ctor var (" ++ x ++ ")")
term2fgg g (TmCtor x as y) =
  map (\ (a, atp) -> term2fgg g a) as +*>= \ xss ->
  let (ns, [iy] : ias : ixss) = combine ([y] : map snd as : map (map snd) xss)
      es = Edge (ias ++ [iy]) (ctorFactorNameDefault x (map snd as) y) :
           map (\ (ixs, (a, _), itp) -> Edge (ixs ++ [itp]) (show a)) (zip3 ixss as ias)
      xs = concat ixss ++ [iy]
      Just cs = ctxtLookupType' g y
      cix = foldr (\ (Ctor x' _) next ix -> if x == x' then ix else next (ix + 1)) id cs 0 in
  addRule' (TmCtor x as y) ns es xs
term2fgg g (TmLam x tp tm tp') =
  lamRule True x tp tm tp' (term2fgg (ctxtDeclTerm g x tp) tm)
term2fgg g (TmApp tm1 tm2 tp2 tp) =
  tmapp2fgg g (TmApp tm1 tm2 tp2 tp)
term2fgg g (TmCase tm y cs tp) =
  term2fgg g tm +>= \ xs ->
  bindCases (map (caseRule g xs (TmCase tm y cs tp)) cs)
  --foldr (\ c r -> caseRule g xs (TmCase tm y cs tp) c +> r) returnRule cs
term2fgg g (TmSamp d tp) =
  let dvs = domainValues g tp
      dvws = vectorWeight dvs in
  case d of
    DistFail ->
      addFactor (show $ TmSamp d tp) (ThisWeight (fmap (const 0) dvws))
    DistUni  ->
      addFactor (show $ TmSamp d tp) (ThisWeight (fmap (const (1.0 / fromIntegral (length dvs))) dvws))
      -- +> addRule' (TmSamp d tp) [tp] [] [0]
    DistAmb  ->  -- TODO: need to change this rule, bc doesn't show up as factor (it shows up as a nonterminal)
      addFactor (show $ TmSamp d tp) (ThisWeight (fmap (const 1) dvws))
      -- +> addRule' (TmSamp d tp) [tp] [] [0]

-- Goes through a program and adds all the rules for it
prog2fgg :: Ctxt -> Progs -> RuleM
prog2fgg g (ProgExec tm) = term2fgg g tm
prog2fgg g (ProgFun x tp tm ps) =
  prog2fgg g ps +> term2fgg g tm +> addRule' (TmVar x tp ScopeGlobal) [tp] [Edge [0] (show tm)] [0]
prog2fgg g (ProgExtern x tp ps) =
  let dvs = domainValues g tp
      dvws = vectorWeight dvs in
  prog2fgg g ps +> addFactor x (ThisWeight (fmap (const 0) dvws))
  -- addNonterm x tp
prog2fgg g (ProgData y cs ps) =
  prog2fgg g ps +> ctorsRules g cs (TpVar y)

-- Computes a list of all the possible inhabitants of a type
domainValues :: Ctxt -> Type -> [String]
domainValues g = tpVals where
  arrVals :: [Type] -> Type -> [String]
  arrVals tps tp =
    map (parensIf (not $ null tps)) $
      foldl (\ ds tp -> kronwith (\ da d -> d ++ " -> " ++ da) ds (domainValues g tp))
        (tpVals tp) tps
  
  tpVals :: Type -> [String]
  tpVals (TpVar y) =
    maybe2 (ctxtLookupType g y) [] $ \ cs ->
      concat $ flip map cs $ \ (Ctor x as) ->
        foldl (kronwith $ \ d da -> d ++ " " ++ parens da)
          [x] (map tpVals as)
  tpVals (TpArr tp1 tp2) = uncurry arrVals (splitArrows (TpArr tp1 tp2))
  tpVals TpBool = [tmFalseName, tmTrueName]
  tpVals (TpMaybe tp) =
    tmNothingName : map (\ tp -> "(" ++ tmJustName ++ " " ++ tp ++ ")") (tpVals tp)

domainSize :: Ctxt -> Type -> Int
domainSize g = length . domainValues g

addMaybeFactors :: Ctxt -> [Type] -> RuleM
addMaybeFactors g (tp : []) = ctorsRules g (maybeCtors tp) (TpMaybe tp)

addBoolFactors :: Ctxt -> [Type] -> RuleM
addBoolFactors g [] = ctorsRules g boolCtors TpBool

data InternalCtor = InternalCtor String (Ctxt -> [Type] -> RuleM) Int {- Num of type args -}
boolInternalCtor = InternalCtor tpBoolName addBoolFactors 0
maybeInternalCtor = InternalCtor tpMaybeName addMaybeFactors 1

addInternalFactors :: Ctxt -> Progs -> RuleM
addInternalFactors g ps =
  let internals = [boolInternalCtor, maybeInternalCtor]
      insts = getPolyInsts ps in
  foldr (\ (InternalCtor name addFs len) rm ->
           let tps = insts name
               msg = ("Expected " ++ show len ++ " type args for "
                        ++ name ++ ", but got " ++ show (length tps)) in
             foldr (\ as rm' -> if len == length as then addFs g as +> rm' else error msg) rm tps) returnRule internals

-- Converts an elaborated program into an FGG
file2fgg :: Ctxt -> Progs -> FGG_JSON
file2fgg g ps =
  let RuleM rs xs nts fs = addInternalFactors g ps +> prog2fgg g ps in
    rulesToFGG (domainValues g) (show $ getStartTerm ps) (reverse rs) nts fs
