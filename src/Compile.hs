module Compile where
import Data.List
import qualified Data.Map as Map
import Exprs
import FGG
import Util
import RuleM
import Ctxt
--import Free
import Name
import Show
import Tensor
import Subst

-- If the start term is just a factor (has no rule), then we need to
-- add a rule [%start%]-(v) -> [tm]-(v)
addStartRuleIfNecessary :: Term -> RuleM -> (String, RuleM)
addStartRuleIfNecessary tm rm =
  let stm = show tm
      tp = getType tm
      [vtp] = newNames [tp] in
    if isRule stm rm then (stm, rm) else
      (startName,
       mkRule (TmVarL startName tp) [vtp] [Edge' [vtp] stm] [vtp] +> rm)

-- Local var rule
varRule :: Var -> Type -> RuleM
varRule x tp =
  let [v0, v1] = newNames [tp, tp] in
    mkRule (TmVarL x tp) [v0, v1] [Edge' [v0, v1] (typeFactorName tp)] [v0, v1]

-- Bind a list of external nodes, and add rules for them
bindExts :: Bool -> [Param] -> RuleM -> RuleM
bindExts addVarRules xs' (RuleM rs xs nts fs) =
  let keep x = not (elem (fst x) (fsts xs'))
      rm = RuleM rs (filter keep xs) nts fs in
    if addVarRules
      then foldr (\ (x, tp) r -> varRule x tp +> r) rm xs'
      else rm

-- Bind an external node, and add a rule for it
bindExt :: Bool -> Var -> Type -> RuleM -> RuleM
bindExt addVarRule x tp = bindExts addVarRule [(x, tp)]

-- Only takes the external nodes from one of the cases,
-- because they should all have the same externals and
-- we don't want to include them more than once.
bindCases :: [External] -> [RuleM] -> RuleM
bindCases xs =
  setExts xs . foldr (\ rm rm' -> rm +> {-resetExts-} rm') returnRule

-- Creates dangling edges that discard a set of nodes
discardEdges' :: [(Var, Type)] -> [(Var, Type)] -> [Edge']
discardEdges' d_xs d_ns = [Edge' [(x, tp), vn] x | ((x, tp), vn) <- zip d_xs d_ns]

-- Pick throwaway var names
newNames :: [a] -> [(Var, a)]
newNames as = [(" " ++ show j, atp) | (j, atp) <- enumerate as]

-- mkRule creates a rule from a lhs term, a list of nodes, and a function that returns the edges and external nodes given a list of the nodes' indices (it does some magic on the nodes, so the indices are not necessarily in the same order as the nodes)
mkRule :: Term -> [(Var, Type)] -> [Edge'] -> [(Var, Type)] -> RuleM
mkRule = mkRuleReps 1

-- Creates this rule `reps` times
mkRuleReps :: Int -> Term -> [(Var, Type)] -> [Edge'] -> [(Var, Type)] -> RuleM
mkRuleReps reps lhs ns es xs =
  addRule reps (Rule (show lhs) (castHGF (HGF' (nub ns) es xs)))


-- Add rule for a constructor
ctorRules :: Ctxt -> Ctor -> Type -> [Ctor] -> RuleM
ctorRules g (Ctor x as) y cs =
  let as' = [(etaName x i, a) | (i, a) <- enumerate as]
      tm = TmVarG CtorVar x [] [(TmVarL a atp, atp) | (a, atp) <- as'] y
      fac = ctorFactorNameDefault x as y in
    addFactor fac (getCtorWeightsFlat (domainValues g) (Ctor x as) cs) +>
    foldr (\ tp r -> type2fgg g tp +> r) returnRule as +>
    let [vy] = newNames [y] in
      mkRule tm (vy : as') [Edge' (as' ++ [vy]) fac] (as' ++ [vy])

-- Add a rule for this particular case in a case-of statement
caseRule :: Ctxt -> FreeVars -> [External] -> Term -> Var -> [Case] -> Type -> Case -> RuleM
caseRule g all_fvs xs_ctm ctm y cs tp (Case x as xtm) =
  bindExts True as $
  term2fgg (ctxtDeclArgs g as) xtm +>= \ xs_xtm_as ->
  let all_xs = Map.toList all_fvs
      unused_ps = Map.toList (Map.difference all_fvs (Map.fromList xs_xtm_as))
      vctp : vtp : unused_nps = newNames (TpVar y : tp : snds unused_ps)
      fac = ctorFactorName x (paramsToArgs (nameParams x (snds as))) (TpVar y)
  in
    mkRule (TmCase ctm y cs tp)
      (vctp : vtp : xs_xtm_as ++ as ++ xs_ctm ++ all_xs ++ unused_ps ++ unused_nps)
      (Edge' (xs_ctm ++ [vctp]) (show ctm) :
       Edge' (xs_xtm_as ++ [vtp]) (show xtm) :
       Edge' (as ++ [vctp]) fac :
       discardEdges' unused_ps unused_nps)
      (xs_ctm ++ all_xs ++ [vtp])

ambRule :: Ctxt -> FreeVars -> [Term] -> Type -> Term -> Int -> RuleM
ambRule g all_fvs tms tp tm reps =
  term2fgg g tm +>= \ tmxs ->
  let all_xs = Map.toList all_fvs
      unused_tms = Map.toList (Map.difference all_fvs (Map.fromList tmxs))
      vtp : unused_ns = newNames (tp : snds unused_tms)
  in
    mkRuleReps reps (TmAmb tms tp) (vtp : tmxs ++ all_xs ++ unused_tms ++ unused_ns)
      (Edge' (tmxs ++ [vtp]) (show tm) : discardEdges' unused_tms unused_ns)
      (all_xs ++ [vtp])

addAmpFactors :: Ctxt -> [Type] -> RuleM
addAmpFactors g tps =
  let ws = getAmpWeights (domainValues g) tps in
    foldr (\ (i, w) r -> r +> addFactor (ampFactorName tps i) w) returnRule (enumerate ws)

addProdFactors :: Ctxt -> [Type] -> RuleM
addProdFactors g tps =
  let tpvs = [domainValues g tp | tp <- tps] in
    type2fgg g (TpProd Multiplicative tps) +>
    addFactor (prodFactorName tps) (getProdWeightsV tpvs) +>
    foldr (\ (as', w) r -> r +> addFactor (prodFactorName' as') w) returnRule (getProdWeights tpvs)


addPairFactor :: Ctxt -> Type -> Type -> RuleM
addPairFactor g tp tp' = addFactor (pairFactorName tp tp') (getPairWeights (domainSize g tp) (domainSize g tp'))

-- Traverse a term and add all rules for subexpressions
term2fgg :: Ctxt -> Term -> RuleM
term2fgg g (TmVarL x tp) =
  type2fgg g tp +>
  addExt x tp
term2fgg g (TmVarG gv x _ [] tp) =
  returnRule -- If this is a ctor/def with no args, we already add its rule when it gets defined
term2fgg g (TmVarG gv x _ as y) =
  [term2fgg g a | (a, atp) <- as] +>=* \ xss ->
  let (vy : ps) = newNames (y : snds as) in
    mkRule (TmVarG gv x [] as y) (vy : ps ++ concat xss)
      (Edge' (ps ++ [vy]) (if gv == CtorVar then ctorFactorNameDefault x (snds as) y else x) :
        [Edge' (xs ++ [vtp]) (show atm) | (xs, (atm, atp), vtp) <- zip3 xss as ps])
      (concat xss ++ [vy])
term2fgg g (TmLam x tp tm tp') =
  bindExt True x tp
    (term2fgg (ctxtDeclTerm g x tp) tm +>= \ tmxs ->
     addPairFactor g tp tp' +>
     type2fgg g tp +>
     let [vtp', varr] = newNames [tp', TpArr tp tp']
         vtp = (x, tp) in
       mkRule (TmLam x tp tm tp') (vtp : vtp' : varr : tmxs)
         [Edge' (tmxs ++ [vtp']) (show tm), Edge' [vtp, vtp', varr] (pairFactorName tp tp')]
         (delete vtp tmxs ++ [varr]))
term2fgg g (TmApp tm1 tm2 tp2 tp) =
  term2fgg g tm1 +>= \ xs1 ->
  term2fgg g tm2 +>= \ xs2 ->
  let fac = pairFactorName tp2 tp
      [vtp2, vtp, varr] = newNames [tp2, tp, TpArr tp2 tp] in
    addPairFactor g tp2 tp +> --addFactor fac (getPairWeights (domainSize g tp2) (domainSize g tp)) +>
    mkRule (TmApp tm1 tm2 tp2 tp) (vtp2 : vtp : varr : xs1 ++ xs2)
      [Edge' (xs2 ++ [vtp2]) (show tm2),
       Edge' (xs1 ++ [varr]) (show tm1),
       Edge' [vtp2, vtp, varr] fac]
      (xs1 ++ xs2 ++ [vtp])    
term2fgg g (TmCase tm y cs tp) =
  term2fgg g tm +>= \ xs ->
  let fvs = freeVars cs in
    bindCases (Map.toList (Map.union (freeVars tm) fvs)) (map (caseRule g fvs xs tm y cs tp) cs)
term2fgg g (TmSamp d tp) =
  let dvs = domainValues g tp in
  case d of
    DistFail ->
      addFactor (show $ TmSamp d tp)
        (vector [0.0 | _ <- [0..length dvs - 1]])
    DistUni  ->
      addFactor (show $ TmSamp d tp)
        (vector [1.0 / fromIntegral (length dvs) | _ <- [0..length dvs - 1]])
    DistAmb  -> -- TODO: is this fine, or do we need to add a rule with one node and one edge (that has the factor below)?
      addFactor (show $ TmSamp d tp) (vector [1.0 | _ <- [0..length dvs - 1]])
term2fgg g (TmAmb tms tp) =
  let fvs = Map.unions (map freeVars tms) in
    bindCases (Map.toList fvs) (map (uncurry $ ambRule g fvs tms tp) (collectDups tms))
term2fgg g (TmLet x xtm xtp tm tp) =
  term2fgg g xtm +>= \ xtmxs ->
  bindExt True x xtp $
  term2fgg (ctxtDeclTerm g x xtp) tm +>= \ tmxs ->
  let vxtp = (x, xtp)
      [vtp] = newNames [tp] in -- TODO: if unused?
    mkRule (TmLet x xtm xtp tm tp) (vxtp : vtp : xtmxs ++ tmxs)
      [Edge' (xtmxs ++ [vxtp]) (show xtm), Edge' (tmxs ++ [vtp]) (show tm)]
      (xtmxs ++ delete vxtp tmxs ++ [vtp])
term2fgg g (TmProd am as)
  | am == Additive =
    let tps = [tp | (_, tp) <- as] in
      foldr
        (\ (i, (atm, tp)) r -> r +>
          term2fgg g atm +>= \ tmxs ->
          let [vamp, vtp] = newNames [TpProd am tps, tp] in
            mkRule (TmProd am as) (vamp : vtp : tmxs)
              ([Edge' (tmxs ++ [vtp]) (show atm), Edge' [vamp, vtp] (ampFactorName tps i)])
              (tmxs ++ [vamp])
        )
        (addAmpFactors g tps) (enumerate as)
  | otherwise =
    [term2fgg g a | (a, atp) <- as] +>=* \ xss ->
    let tps = snds as
        ptp = TpProd am tps
        (vptp : vtps) = newNames (ptp : tps)
    in
      addProdFactors g tps +>
      mkRule (TmProd am as) (vptp : vtps ++ concat xss)
        (Edge' (vtps ++ [vptp]) (prodFactorName (snds as)) :
          [Edge' (tmxs ++ [vtp]) (show atm) | ((atm, atp), vtp, tmxs) <- zip3 as vtps xss])
        (concat xss ++ [vptp])
term2fgg g (TmElimProd Additive ptm ps tm tp) =
  term2fgg g ptm +>= \ ptmxs ->
  let o = injIndex [x | (x, _) <- ps]
      (x, xtp) = ps !! o in
--    error (show (o, ps))
    bindExt True x xtp $
    term2fgg (ctxtDeclTerm g x xtp) tm +>= \ tmxs ->
    let tps = [tp | (_, tp) <- ps]
        ptp = TpProd Additive tps
        -- unused_ps = if  -- TODO: if unused?
        [vtp, vptp] = newNames [tp, ptp]
    in
      if NoTp `elem` tps then error (show (TmElimProd Additive ptm ps tm tp)) else
      addAmpFactors g tps +>
      mkRule (TmElimProd Additive ptm ps tm tp)
        (vtp : vptp : (x, xtp) : tmxs ++ ptmxs)
        [Edge' (ptmxs ++ [vptp]) (show ptm),
         Edge' (tmxs ++ [vtp]) (show tm),
         Edge' [vptp, (x, xtp)] (ampFactorName tps o)]
        (ptmxs ++ delete (x, xtp) tmxs ++ [vtp])


{-term2fgg g (TmElimProd Additive tm o tp) =
  term2fgg g tm +>= \ tmxs ->
  let tps = case typeof tm of { TpProd am tps -> tps; _ -> error "expected an &-product, when compiling" }
      --tp = tps !! o
      [vtp, vamp] = newNames [tp, TpProd Additive tps] in
    mkRule (TmElimAmp tm o (tps !! fst o)) (vtp : vamp : tmxs)
      ([Edge' (tmxs ++ [vamp]) (show tm), Edge' [vamp, vtp] (ampFactorName tps (fst o))])
      (tmxs ++ [vtp]) +>
    addAmpFactors g tps-}
term2fgg g (TmElimProd Multiplicative ptm ps tm tp) =
  term2fgg g ptm +>= \ ptmxs ->
  bindExts True ps $
  term2fgg (ctxtDeclArgs g ps) tm +>= \ tmxs ->
  let tps = [tp | (_, tp) <- ps]
      ptp = TpProd Multiplicative tps
      unused_ps = Map.toList (Map.difference (Map.fromList ps) (Map.fromList tmxs))
      vtp : vptp : unused_nps = newNames (tp : ptp : snds unused_ps)
  in
    addProdFactors g tps +>
    mkRule (TmElimProd Multiplicative ptm ps tm tp)
      (vtp : vptp : ps ++ unused_ps ++ unused_nps ++ tmxs ++ ptmxs)
         (Edge' (ptmxs ++ [vptp]) (show ptm) :
            Edge' (ps ++ [vptp]) (prodFactorName tps) :
            Edge' (tmxs ++ [vtp]) (show tm) :
            discardEdges' unused_ps unused_nps)
         (ptmxs ++ foldr delete tmxs ps ++ [vtp])
term2fgg g (TmEqs tms) =
  [term2fgg g tm | tm <- tms] +>=* \ xss ->
  let tmstp = getType (head tms)
      ntms = length tms
      fac = eqFactorName tmstp ntms
      (vbtp : vtps) = newNames (TpVar "Bool" : [getType tm | tm <- tms]) in
    addFactor fac (getEqWeights (domainSize g tmstp) ntms) +>
    mkRule (TmEqs tms)
      (vbtp : vtps ++ concat xss)
      (Edge' (vtps ++ [vbtp]) fac : [Edge' (xs ++ [vtp]) (show tm) | (tm, vtp, xs) <- zip3 tms vtps xss])
      (concat xss ++ [vbtp])

type2fgg :: Ctxt -> Type -> RuleM
type2fgg g tp =
  addFactor (typeFactorName tp) (getCtorEqWeights (domainSize g tp)) +>
  type2fgg' g tp

type2fgg' :: Ctxt -> Type -> RuleM
type2fgg' g (TpVar y) = returnRule
type2fgg' g (TpArr tp1 tp2) = type2fgg g tp1 +> type2fgg g tp2
type2fgg' g (TpProd am tps) = foldr (\ tp r -> r +> type2fgg g tp) returnRule tps
type2fgg' g NoTp = error "Compiling NoTp to FGG rule"


-- Adds the rules for a Prog
prog2fgg :: Ctxt -> Prog -> RuleM
prog2fgg g (ProgFun x ps tm tp) =
  type2fgg g (joinArrows (snds ps) tp) +>= \ _ ->
  bindExts True ps $ term2fgg (ctxtDeclArgs g ps) tm +>= \ tmxs ->
  let unused_ps = Map.toList (Map.difference (Map.fromList ps) (Map.fromList tmxs))
      (unused_x, unused_tp) = unzip unused_ps
      vtp : unused_n = newNames (tp : unused_tp)
  in
    mkRule (TmVarG DefVar x [] [] tp) (vtp : tmxs ++ ps ++ unused_n ++ unused_ps)
      (Edge' (tmxs ++ [vtp]) (show tm) : discardEdges' unused_ps unused_n)
      (ps ++ [vtp])
prog2fgg g (ProgExtern x ps tp) =
  let tp' = (joinArrows ps tp) in
    type2fgg g tp' +>
    -- addNonterm x tp' +>
    addIncompleteFactor x
  {-
  type2fgg g (joinArrows ps tp) +>= \ _ ->
  let (vtp : vps) = newNames (tp : ps) in
    mkRule (TmVarG DefVar x [] tp) (vtp : vps)
      [Edge' (vps ++ [vtp]) xp]
      (vps ++ [vtp]) +>
    addFactor xp (getExternWeights (domainValues g) ps tp)
  -}
prog2fgg g (ProgData y cs) =
  foldr (\ (fac, ws) rm -> addFactor fac ws +> rm) returnRule
    (getCtorWeightsAll (domainValues g) cs (TpVar y)) +>
  foldr (\ (Ctor x as) r -> r +> ctorRules g (Ctor x as) (TpVar y) cs) returnRule cs +>
  type2fgg g (TpVar y)

-- Goes through a program and adds all the rules for it
progs2fgg :: Ctxt -> Progs -> RuleM
progs2fgg g (Progs ps tm) =
  foldr (\ p rm -> rm +> prog2fgg g p) (term2fgg g tm) ps
  

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
      concat [foldl (kronwith $ \ d da -> d ++ " " ++ parens da) [x] (map tpVals as)
             | (Ctor x as) <- cs]
  tpVals (TpArr tp1 tp2) = uncurry arrVals (splitArrows (TpArr tp1 tp2))
  tpVals (TpProd am tps)
    | am == Additive =
      let tpvs = map tpVals tps in
        concatMap (\ (i, vs) -> ["<" ++ delimitWith ", " [show tp | tp <- tps] ++ ">." ++ show i ++ "=" ++ tmv | tmv <- vs]) (enumerate tpvs)
    | otherwise =
      [prodValName' tmvs | tmvs <- kronall [tpVals tp | tp <- tps]]
  tpVals NoTp = error ("Enumerating values of a NoTp: " ++ show (Map.keys g))

domainSize :: Ctxt -> Type -> Int
domainSize g = length . domainValues g

-- Converts an elaborated program into an FGG
compileFile :: Progs -> Either String String
compileFile ps =
  let g = ctxtDefProgs ps
      Progs _ end = ps
      rm = progs2fgg g ps
      (end', RuleM rs xs nts fs) = addStartRuleIfNecessary end rm in
    return (show (rulesToFGG (domainValues g) end' (reverse rs) nts fs))
