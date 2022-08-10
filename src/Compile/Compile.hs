module Compile.Compile where
import Data.List
import qualified Data.Map as Map
import Compile.RuleM
import Util.Tensor
import Util.FGG
import Util.Helpers
import Struct.Lib
import Scope.Ctxt (Ctxt, ctxtDefProgs, ctxtDeclArgs, ctxtDefLocal, ctxtLookupType)
import Scope.Name
import Scope.Subst (FreeVars, freeVars)

-- Pick throwaway node names (doesn't really matter what these are,
-- so long as they're different from each other and don't conflict
-- with any other names in the FGG rule
newNodeNames :: [a] -> [(NodeName, a)]
newNodeNames as = [(NodeName (" " ++ show j), atp) | (j, atp) <- enumerate as]

nonterminalLabel :: Term -> EdgeLabel
nonterminalLabel = EdgeLabel . show

paramsToExternals :: [Param] -> [External]
paramsToExternals ps = [(NodeName x, tp) | (x, tp) <- ps]


{- varRule x tp

   Create rule for local variable x:

     (v0)-[x]-(v1) -> (v0)-[v0=v1]-(v1)
 -}

varRule :: Var -> Type -> RuleM
varRule x tp =
  let [v0, v1] = newNodeNames [tp, tp] in
    mkRule (TmVarL x tp) [v0, v1] [Edge [v0, v1] (EdgeLabel (typeFactorName tp))] [v0, v1]

{- bindExts xs' rm

   Run rm, and for each variable x in xs', make x internal and create a rule for x. -}
    
bindExts :: [Param] -> RuleM -> RuleM
bindExts xs' (RuleM rs xs nts fs) =
  let keep (NodeName x, _) = not (elem x (fsts xs'))
      rm = RuleM rs (filter keep xs) nts fs in
    foldr (\ (x, tp) r -> varRule x tp +> r) rm xs'

{- bindExt addVarRule x tp rm

   Like bindExt, but for a single variable. -}
    
bindExt :: Var -> Type -> RuleM -> RuleM
bindExt x tp = bindExts [(x, tp)]

{- bindCases xs rms

   Runs all of rms and keeps only the external nodes in xs. -}
                          
bindCases :: [Param] -> [RuleM] -> RuleM
bindCases xs =
  setExts (paramsToExternals xs) . foldr (\ rm rm' -> rm +> rm') returnRule

{- mkRule lhs ns es xs

Creates a rule.

- lhs: the left-hand side
- ns:  the right-hand side node ids and labels
- es:  the right-hand side edges
- xs:  the external node ids and labels -}

mkRule :: Term -> [(NodeName, Type)] -> [Edge Type] -> [External] -> RuleM
mkRule = mkRuleReps 1

-- Creates this rule `reps` times
mkRuleReps :: Int -> Term -> [(NodeName, Type)] -> [Edge Type] -> [External] -> RuleM
mkRuleReps reps lhs ns es xs =
  addRule reps (Rule (nonterminalLabel lhs) (HGF (nub ns) es (nub xs)))


-- Add rule for a constructor
ctorRules :: Ctxt -> Ctor -> Type -> [Ctor] -> RuleM
ctorRules g (Ctor x as) y cs =
  let as' = [(etaName x i, a) | (i, a) <- enumerate as]
      tm = TmVarG CtorVar x [] [] [(TmVarL a atp, atp) | (a, atp) <- as'] y
      fac = EdgeLabel (ctorFactorNameDefault x as y) in
    addFactor fac (getCtorWeightsFlat (domainValues g) (Ctor x as) cs) +>
    foldr (\ tp r -> type2fgg g tp +> r) returnRule as +>
    let [vy] = newNodeNames [y]
        as'' = paramsToExternals as' in
      mkRule tm (vy : as'') [Edge (as'' ++ [vy]) fac] (as'' ++ [vy])

-- Add a rule for this particular case in a case-of statement
caseRule :: Ctxt -> FreeVars -> [External] -> Term -> Var -> [Case] -> Type -> Case -> RuleM
caseRule g all_fvs xs_ctm ctm y cs tp (Case x as xtm) =
  bindExts as $
  term2fgg (ctxtDeclArgs g as) xtm +>= \ xs_xtm_as ->
  let all_xs = paramsToExternals (Map.toList all_fvs)
      unused_ps = Map.toList (Map.difference (Map.fromList all_xs) (Map.fromList xs_xtm_as))
      [vctp, vtp] = newNodeNames [TpData y [] [], tp]
      fac = EdgeLabel (ctorFactorName x (paramsToArgs (nameParams x (snds as))) (TpData y [] []))
      as' = paramsToExternals as
  in
    mkRule (TmCase ctm (y, [], []) cs tp)
      (vctp : vtp : xs_xtm_as ++ as' ++ xs_ctm ++ all_xs ++ unused_ps)
      [Edge (xs_ctm ++ [vctp]) (nonterminalLabel ctm),
       Edge (xs_xtm_as ++ [vtp]) (nonterminalLabel xtm),
       Edge (as' ++ [vctp]) fac]
      (xs_ctm ++ all_xs ++ [vtp])

-- Adds rule for the i-th term in an amb tm1 tm2 ... tmn
ambRule :: Ctxt -> FreeVars -> [Term] -> Type -> Term -> Int -> RuleM
ambRule g all_fvs tms tp tm reps =
  term2fgg g tm +>= \ tmxs ->
  let all_xs = paramsToExternals (Map.toList all_fvs)
      unused_tms = Map.toList (Map.difference (Map.fromList all_xs) (Map.fromList tmxs))
      [vtp] = newNodeNames [tp]
  in
    mkRuleReps reps (TmAmb tms tp) (vtp : tmxs ++ all_xs ++ unused_tms)
      [Edge (tmxs ++ [vtp]) (nonterminalLabel tm)]
      (all_xs ++ [vtp])

-- Adds rule for the i-th component of an &-product
ampRule :: Ctxt -> FreeVars -> [Arg] -> Int -> Term -> Type -> RuleM
ampRule g all_fvs as i tm tp =
  term2fgg g tm +>= \ tmxs ->
  let tps = snds as
      all_xs = paramsToExternals (Map.toList all_fvs)
      unused_tms = Map.toList (Map.difference (Map.fromList all_xs) (Map.fromList tmxs))
      [vamp, vtp] = newNodeNames [TpProd Additive tps, tp]
  in
    mkRule (TmProd Additive as) (vamp : vtp : tmxs ++ all_xs ++ unused_tms)
      [Edge (tmxs ++ [vtp]) (nonterminalLabel tm),
       Edge [vamp, vtp] (EdgeLabel (ampFactorName tps i))]
      (all_xs ++ [vamp])

-- Adds factors for the &-product of tps
addAmpFactors :: Ctxt -> [Type] -> RuleM
addAmpFactors g tps =
  let ws = getAmpWeights (map (domainValues g) tps) in
    foldr (\ (i, w) r -> r +> addFactor (EdgeLabel (ampFactorName tps i)) w) returnRule (enumerate ws)

-- Adds factors for the *-product of tps
addProdFactors :: Ctxt -> [Type] -> RuleM
addProdFactors g tps =
  let tpvs = [domainValues g tp | tp <- tps] in
    type2fgg g (TpProd Multiplicative tps) +>
    addFactor (EdgeLabel (prodFactorName tps)) (getProdWeightsV tpvs) +>
    foldr (\ (as', w) r -> r +> addFactor (EdgeLabel (prodFactorName' [a | Value a <- as'])) w) returnRule (getProdWeights tpvs)

-- Adds factor for v=(tp -> tp')
addPairFactor :: Ctxt -> Type -> Type -> RuleM
addPairFactor g tp tp' = addFactor (EdgeLabel (pairFactorName tp tp')) (getPairWeights (domainSize g tp) (domainSize g tp'))

{- term2fgg g tm

   Traverse a term tm and add rules for it and all its subexpressions.

   Returns: A RuleM containing the rules, with an external node
   for each free variable in tm. -}

term2fgg :: Ctxt -> Term -> RuleM

-- The rule for local variables is already created in bindExt(s).
term2fgg g (TmVarL x tp) =
  type2fgg g tp +>
  addExt (NodeName x) tp

term2fgg g (TmVarG gv x [] [] [] tp) =
  returnRule -- If this is a ctor/def with no args, we already add its rule when it gets defined

term2fgg g (TmVarG gv x [] [] as y) =
  [term2fgg g a | (a, atp) <- as] +>=* \ xss ->
  let (vy : ps) = newNodeNames (y : snds as)
      el = case gv of CtorVar -> EdgeLabel (ctorFactorNameDefault x (snds as) y)
                      DefVar -> EdgeLabel x
  in
    mkRule (TmVarG gv x [] [] as y) (vy : ps ++ concat xss)
      (Edge (ps ++ [vy]) el :
        [Edge (xs ++ [vtp]) (nonterminalLabel atm) | (xs, (atm, atp), vtp) <- zip3 xss as ps])
      (concat xss ++ [vy])

term2fgg _ (TmVarG _ _ _ _ _ _) = error "Cannot compile polymorphic code"

term2fgg g (TmLam x tp tm tp') =
  bindExt x tp
    (term2fgg (ctxtDefLocal g x tp) tm +>= \ tmxs ->
     addPairFactor g tp tp' +>
     type2fgg g tp +>
     let [vtp', varr] = newNodeNames [tp', TpArr tp tp']
         vtp = (NodeName x, tp) in
       mkRule (TmLam x tp tm tp') (vtp : vtp' : varr : tmxs)
         [Edge (tmxs ++ [vtp']) (nonterminalLabel tm),
          Edge [vtp, vtp', varr] (EdgeLabel (pairFactorName tp tp'))]
         (delete vtp tmxs ++ [varr]))

term2fgg g (TmApp tm1 tm2 tp2 tp) =
  term2fgg g tm1 +>= \ xs1 ->
  term2fgg g tm2 +>= \ xs2 ->
  let fac = EdgeLabel (pairFactorName tp2 tp)
      [vtp2, vtp, varr] = newNodeNames [tp2, tp, TpArr tp2 tp] in
    addPairFactor g tp2 tp +>
    mkRule (TmApp tm1 tm2 tp2 tp) (vtp2 : vtp : varr : xs1 ++ xs2)
      [Edge (xs2 ++ [vtp2]) (nonterminalLabel tm2),
       Edge (xs1 ++ [varr]) (nonterminalLabel tm1),
       Edge [vtp2, vtp, varr] fac]
      (xs1 ++ xs2 ++ [vtp])    

term2fgg g (TmCase tm (y, [], []) cs tp) =
  term2fgg g tm +>= \ xs ->
  let fvs = freeVars cs in
    bindCases (Map.toList (Map.union (freeVars tm) fvs)) (map (caseRule g fvs xs tm y cs tp) cs)

term2fgg _ (TmCase _ _ _ _) = error "Cannot compile polymorphic code"

-- fail (i.e., amb with no arguments) doesn't generate any rules, but
-- should still generate the left-hand side nonterminal
term2fgg g (TmAmb [] tp) = addNonterm (nonterminalLabel (TmAmb [] tp)) [tp]
term2fgg g (TmAmb tms tp) =
  let fvs = Map.unions (map freeVars tms) in
    bindCases (Map.toList fvs) (map (uncurry $ ambRule g fvs tms tp) (collectDups tms))
    
term2fgg g (TmFactor wt tm tp) =
  term2fgg g tm +>= \ xs ->
  let [vtp] = newNodeNames [tp]
      el = EdgeLabel ("factor " ++ show wt) in
  addFactor el (Scalar wt) +>
  mkRule (TmFactor wt tm tp) (vtp : xs)
    [Edge [] el,
     Edge (xs ++ [vtp]) (nonterminalLabel tm)]
    (xs ++ [vtp])
  
term2fgg g (TmLet x xtm xtp tm tp) =
  term2fgg g xtm +>= \ xtmxs ->
  bindExt x xtp $
  term2fgg (ctxtDefLocal g x xtp) tm +>= \ tmxs ->
  let vxtp = (NodeName x, xtp)
      [vtp] = newNodeNames [tp] in -- TODO: if unused?
    mkRule (TmLet x xtm xtp tm tp) (vxtp : vtp : xtmxs ++ tmxs)
      [Edge (xtmxs ++ [vxtp]) (nonterminalLabel xtm),
       Edge (tmxs ++ [vtp]) (nonterminalLabel tm)]
      (xtmxs ++ delete vxtp tmxs ++ [vtp])

term2fgg g (TmProd Additive as) =
  -- Technically a 0-ary additive product (<>) can be constructed but not destructed.
  -- But linearity requires that every additive product be destructed exactly once,
  -- so don't bother creating any FGG rules for <>.
  let (tms, tps) = unzip as
      fvs = freeVars tms in
    addAmpFactors g tps +>
    bindCases (Map.toList fvs) [ampRule g fvs as i atm tp | (i, (atm, tp)) <- enumerate as]
    
term2fgg g (TmProd am@Multiplicative as) =
  [term2fgg g a | (a, atp) <- as] +>=* \ xss ->
  let tps = snds as
      ptp = TpProd am tps
      (vptp : vtps) = newNodeNames (ptp : tps)
  in
    addProdFactors g tps +>
    mkRule (TmProd am as) (vptp : vtps ++ concat xss)
      (Edge (vtps ++ [vptp]) (EdgeLabel (prodFactorName (snds as))) :
        [Edge (tmxs ++ [vtp]) (nonterminalLabel atm) | ((atm, atp), vtp, tmxs) <- zip3 as vtps xss])
      (concat xss ++ [vptp])

term2fgg g (TmElimProd Additive ptm ps tm tp) =
  term2fgg g ptm +>= \ ptmxs ->
  let o = injIndex [x | (x, _) <- ps]
      (x, xtp) = ps !! o in
    bindExt x xtp $
    term2fgg (ctxtDefLocal g x xtp) tm +>= \ tmxs ->
    let x' = NodeName x
        tps = snds ps
        ptp = TpProd Additive tps
        [vtp, vptp] = newNodeNames [tp, ptp]
    in
      addAmpFactors g tps +>
      mkRule (TmElimProd Additive ptm ps tm tp)
        (vtp : vptp : (x', xtp) : tmxs ++ ptmxs)
        [Edge (ptmxs ++ [vptp]) (nonterminalLabel ptm),
         Edge (tmxs ++ [vtp]) (nonterminalLabel tm),
         Edge [vptp, (x', xtp)] (EdgeLabel (ampFactorName tps o))]
        (ptmxs ++ delete (x', xtp) tmxs ++ [vtp])

term2fgg g (TmElimProd Multiplicative ptm ps tm tp) =
  term2fgg g ptm +>= \ ptmxs ->
  bindExts ps $
  term2fgg (ctxtDeclArgs g ps) tm +>= \ tmxs ->
  let ps' = paramsToExternals ps
      tps = snds ps
      ptp = TpProd Multiplicative tps
      unused_ps = Map.toList (Map.difference (Map.fromList ps') (Map.fromList tmxs))
      [vtp, vptp] = newNodeNames [tp, ptp]
  in
    addProdFactors g tps +>
    mkRule (TmElimProd Multiplicative ptm ps tm tp)
      (vtp : vptp : ps' ++ unused_ps ++ tmxs ++ ptmxs)
      [Edge (ptmxs ++ [vptp]) (nonterminalLabel ptm),
       Edge (ps' ++ [vptp]) (EdgeLabel (prodFactorName tps)),
       Edge (tmxs ++ [vtp]) (nonterminalLabel tm)]
         (ptmxs ++ foldr delete tmxs ps' ++ [vtp])

term2fgg g (TmEqs tms) =
  [term2fgg g tm | tm <- tms] +>=* \ xss ->
  let tmstp = typeof (head tms)
      ntms = length tms
      fac = EdgeLabel (eqFactorName tmstp ntms)
      (vbtp : vtps) = newNodeNames (tpBool : [typeof tm | tm <- tms]) in
    addFactor fac (getEqWeights (domainSize g tmstp) ntms) +>
    mkRule (TmEqs tms)
      (vbtp : vtps ++ concat xss)
      (Edge (vtps ++ [vbtp]) fac : [Edge (xs ++ [vtp]) (nonterminalLabel tm) | (tm, vtp, xs) <- zip3 tms vtps xss])
      (concat xss ++ [vbtp])

-- Adds factors for each subexpression in a type
type2fgg :: Ctxt -> Type -> RuleM
type2fgg g tp =
  addFactor (EdgeLabel (typeFactorName tp)) (getCtorEqWeights (domainSize g tp)) +>
  type2fgg' g tp
  where
    type2fgg' :: Ctxt -> Type -> RuleM
    type2fgg' g (TpData y [] []) = returnRule
    type2fgg' g (TpArr tp1 tp2) = type2fgg g tp1 +> type2fgg g tp2
    type2fgg' g (TpProd am tps) = foldr (\ tp r -> r +> type2fgg g tp) returnRule tps
    type2fgg' g tp = error ("Compiling a " ++ show tp ++ " to FGG rule")


-- Adds the rules for a Prog
prog2fgg :: Ctxt -> Prog -> RuleM
prog2fgg g (ProgFun x ps tm tp) =
  type2fgg g (joinArrows (snds ps) tp) +>= \ _ ->
  bindExts ps $ term2fgg (ctxtDeclArgs g ps) tm +>= \ tmxs ->
  let ps' = paramsToExternals ps
      unused_ps = Map.toList (Map.difference (Map.fromList ps') (Map.fromList tmxs))
      (unused_x, unused_tp) = unzip unused_ps
      [vtp] = newNodeNames [tp]
  in
    mkRule (TmVarG DefVar x [] [] [] tp) (vtp : tmxs ++ ps' ++ unused_ps)
      (Edge (tmxs ++ [vtp]) (nonterminalLabel tm) : [])
      (ps' ++ [vtp])
prog2fgg g (ProgExtern x ps tp) =
  let tp' = (joinArrows ps tp) in
    type2fgg g tp' +>
    addIncompleteFactor (EdgeLabel x)
prog2fgg g (ProgData y cs) =
  -- Add constructor factors
  foldr (\ (fac, ws) rm -> addFactor fac ws +> rm) returnRule
    (getCtorWeightsAll (domainValues g) cs (TpData y [] [])) +>
  -- Add constructor rules
  foldr (\ (Ctor x as) r -> r +> ctorRules g (Ctor x as) (TpData y [] []) cs) returnRule cs +>
  type2fgg g (TpData y [] [])

-- Goes through a program and adds all the rules for it
progs2fgg :: Ctxt -> Progs -> RuleM
progs2fgg g (Progs ps tm) =
  foldr (\ p rm -> rm +> prog2fgg g p) (term2fgg g tm) ps
  

-- Computes a list of all the possible inhabitants of a type
domainValues :: Ctxt -> Type -> [Value]
domainValues g tp = Value <$> domainValues' g tp

domainValues' :: Ctxt -> Type -> [String]
domainValues' g = tpVals where
  arrVals :: [Type] -> Type -> [String]
  arrVals tps tp =
    map (parensIf (not $ null tps)) $
      foldl (\ ds tp -> kronwith (\ da d -> d ++ " -> " ++ da) ds (domainValues' g tp))
        (tpVals tp) tps
  
  tpVals :: Type -> [String]
  tpVals (TpData y [] []) =
    maybe2 (ctxtLookupType g y) [] $ \ cs ->
      concat [foldl (kronwith $ \ d da -> d ++ " " ++ parens da) [x] (map tpVals as)
             | (Ctor x as) <- cs]
  tpVals (TpArr tp1 tp2) = uncurry arrVals (splitArrows (TpArr tp1 tp2))
  tpVals (TpProd Additive tps) =
    -- The type of 0-ary additive tuples has no values, but this
    -- is never going to happen anyway.
    let tpvs = map tpVals tps in
      concatMap (\ (i, vs) -> ["<" ++ intercalate ", " [show tp | tp <- tps] ++ ">." ++ show i ++ "=" ++ tmv | tmv <- vs]) (enumerate tpvs)
  tpVals (TpProd Multiplicative tps) =
    [prodValName' tmvs | tmvs <- kronall [tpVals tp | tp <- tps]]
  tpVals tp = error ("Enumerating values of a " ++ show tp)

domainSize :: Ctxt -> Type -> Int
domainSize g = length . domainValues g

-- Converts an elaborated program into an FGG
compileFile :: Progs -> Either String FGG
compileFile ps =
  let g = ctxtDefProgs ps
      Progs _ end = ps
      RuleM rs xs nts fs = progs2fgg g ps
  in
      return (rulesToFGG (domainValues g) (nonterminalLabel end) (reverse rs) nts fs)
