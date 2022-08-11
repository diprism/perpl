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

newNodeNames :: [a] -> [(NodeName, a)]
newNodeNames as = [(NnInternal j, atp) | (j, atp) <- enumerate as]

paramsToExternals :: [Param] -> [External]
paramsToExternals ps = [(NnVar x, tp) | (x, tp) <- ps]

unusedExternals :: [External] -> [External] -> [External]
unusedExternals = deleteFirstsBy (\ (x1, _) (x2, _) -> x1 == x2)


{- varRule x tp

   Create rule for local variable x:

     (v0)-[x]-(v1) -> (v0)-[v0=v1]-(v1)
 -}

varRule :: Var -> Type -> RuleM
varRule x tp = let ns = [(NnVar x, tp), (NnOut, tp)] in
  mkRule (TmVarL x tp) ns [Edge ns (ElTerminal (typeFactorName tp))] ns

{- bindExts xs' rm

   Run rm, and for each variable x in xs', make x internal and create a rule for x. -}
    
bindExts :: [Param] -> RuleM -> RuleM
bindExts xs' (RuleM rs xs nts fs) =
  let keep (NnVar x, _) = not (elem x (fsts xs'))
      keep _ = error "expected an external node"
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

mkRule :: Term -> [(NodeName, Type)] -> [Edge] -> [External] -> RuleM
mkRule = mkRuleReps 1

-- Creates this rule `reps` times
mkRuleReps :: Int -> Term -> [(NodeName, Type)] -> [Edge] -> [External] -> RuleM
mkRuleReps reps lhs ns es xs =
  addRule reps (Rule (ElNonterminal lhs) (HGF (nub ns) es (nub xs)))


-- Add rule for a constructor
ctorRules :: Ctxt -> Ctor -> Type -> [Ctor] -> RuleM
ctorRules g (Ctor x as) y cs =
  let as' = [(etaName x i, a) | (i, a) <- enumerate as]
      tm = TmVarG CtorVar x [] [] [(TmVarL a atp, atp) | (a, atp) <- as'] y
      fac = ElTerminal (ctorFactorName x as y) in
    addFactor fac (getCtorWeightsFlat (domainValues g) (Ctor x as) cs) +>
    foldr (\ tp r -> type2fgg g tp +> r) returnRule as +>
    let vy = (NnOut, y)
        as'' = paramsToExternals as' in
      mkRule tm (vy : as'') [Edge (as'' ++ [vy]) fac] (as'' ++ [vy])

-- Add a rule for this particular case in a case-of statement
caseRule :: Ctxt -> FreeVars -> [External] -> Term -> Var -> [Case] -> Type -> Case -> RuleM
caseRule g all_fvs xs_ctm ctm y cs tp (Case x as xtm) =
  bindExts as $
  term2fgg (ctxtDeclArgs g as) xtm +>= \ xs_xtm_as ->
  let all_xs = paramsToExternals (Map.toList all_fvs)
      unused_ps = unusedExternals all_xs xs_xtm_as
      [vctp] = newNodeNames [TpData y [] []]
      vtp = (NnOut, tp)
      fac = ElTerminal (ctorFactorName x (snds as) (TpData y [] []))
      as' = paramsToExternals as
  in
    mkRule (TmCase ctm (y, [], []) cs tp)
      (vctp : vtp : xs_xtm_as ++ as' ++ xs_ctm ++ all_xs ++ unused_ps)
      [Edge (xs_ctm ++ [vctp]) (ElNonterminal ctm),
       Edge (xs_xtm_as ++ [vtp]) (ElNonterminal xtm),
       Edge (as' ++ [vctp]) fac]
      (xs_ctm ++ all_xs ++ [vtp])

-- Adds rule for the i-th term in an amb tm1 tm2 ... tmn
ambRule :: Ctxt -> FreeVars -> [Term] -> Type -> Term -> Int -> RuleM
ambRule g all_fvs tms tp tm reps =
  term2fgg g tm +>= \ tmxs ->
  let all_xs = paramsToExternals (Map.toList all_fvs)
      unused_tms = unusedExternals all_xs tmxs
      vtp = (NnOut, tp)
  in
    mkRuleReps reps (TmAmb tms tp) (vtp : tmxs ++ all_xs ++ unused_tms)
      [Edge (tmxs ++ [vtp]) (ElNonterminal tm)]
      (all_xs ++ [vtp])

-- Adds rule for the i-th component of an &-product
ampRule :: Ctxt -> FreeVars -> [Arg] -> Int -> Term -> Type -> RuleM
ampRule g all_fvs as i tm tp =
  term2fgg g tm +>= \ tmxs ->
  let tps = snds as
      all_xs = paramsToExternals (Map.toList all_fvs)
      unused_tms = unusedExternals all_xs tmxs
      [vamp] = newNodeNames [TpProd Additive tps]
      vtp = (NnOut, tp)
  in
    mkRule (TmProd Additive as) (vamp : vtp : tmxs ++ all_xs ++ unused_tms)
      [Edge (tmxs ++ [vtp]) (ElNonterminal tm),
       Edge [vamp, vtp] (ElTerminal (ampFactorName tps i))]
      (all_xs ++ [vamp])

-- Adds factors for the &-product of tps
addAmpFactors :: Ctxt -> [Type] -> RuleM
addAmpFactors g tps =
  let ws = getAmpWeights (map (domainValues g) tps) in
    foldr (\ (i, w) r -> r +> addFactor (ElTerminal (ampFactorName tps i)) w) returnRule (enumerate ws)

-- Adds factors for the *-product of tps
addProdFactors :: Ctxt -> [Type] -> RuleM
addProdFactors g tps =
  let tpvs = [domainValues g tp | tp <- tps] in
    type2fgg g (TpProd Multiplicative tps) +>
    addFactor (ElTerminal (prodFactorName tps)) (getProdWeightsV tpvs)

-- Adds factor for v=(tp -> tp')
addPairFactor :: Ctxt -> Type -> Type -> RuleM
addPairFactor g tp tp' = addFactor (ElTerminal (pairFactorName tp tp')) (getPairWeights (domainSize g tp) (domainSize g tp'))

{- term2fgg g tm

   Traverse a term tm and add rules for it and all its subexpressions.

   Returns: A RuleM containing the rules, with an external node
   for each free variable in tm. -}

term2fgg :: Ctxt -> Term -> RuleM

-- The rule for local variables is already created in bindExt(s).
term2fgg g (TmVarL x tp) =
  type2fgg g tp +>
  addExt (NnVar x) tp

term2fgg g (TmVarG gv x [] [] [] tp) =
  returnRule -- If this is a ctor/def with no args, we already add its rule when it gets defined

term2fgg g (TmVarG gv x [] [] as y) =
  [term2fgg g a | (a, atp) <- as] +>=* \ xss ->
  let ps = newNodeNames (snds as)
      vy = (NnOut, y)
      el = case gv of CtorVar -> ElTerminal (ctorFactorName x (snds as) y)
                      DefVar -> ElNonterminal (TmVarG gv x [] [] [] (joinArrows (snds as) y))
  in
    mkRule (TmVarG gv x [] [] as y) (vy : ps ++ concat xss)
      (Edge (ps ++ [vy]) el :
        [Edge (xs ++ [vtp]) (ElNonterminal atm) | (xs, (atm, atp), vtp) <- zip3 xss as ps])
      (concat xss ++ [vy])

term2fgg _ (TmVarG _ _ _ _ _ _) = error "Cannot compile polymorphic code"

term2fgg g (TmLam x tp tm tp') =
  bindExt x tp
    (term2fgg (ctxtDefLocal g x tp) tm +>= \ tmxs ->
     addPairFactor g tp tp' +>
     type2fgg g tp +>
     let [vtp'] = newNodeNames [tp']
         varr = (NnOut, TpArr tp tp')
         vtp = (NnVar x, tp) in
       mkRule (TmLam x tp tm tp') (vtp : vtp' : varr : tmxs)
         [Edge (tmxs ++ [vtp']) (ElNonterminal tm),
          Edge [vtp, vtp', varr] (ElTerminal (pairFactorName tp tp'))]
         (delete vtp tmxs ++ [varr]))

term2fgg g (TmApp tm1 tm2 tp2 tp) =
  term2fgg g tm1 +>= \ xs1 ->
  term2fgg g tm2 +>= \ xs2 ->
  let fac = ElTerminal (pairFactorName tp2 tp)
      vtp = (NnOut, tp)
      [vtp2, varr] = newNodeNames [tp2, TpArr tp2 tp] in
    addPairFactor g tp2 tp +>
    mkRule (TmApp tm1 tm2 tp2 tp) (vtp2 : vtp : varr : xs1 ++ xs2)
      [Edge (xs2 ++ [vtp2]) (ElNonterminal tm2),
       Edge (xs1 ++ [varr]) (ElNonterminal tm1),
       Edge [vtp2, vtp, varr] fac]
      (xs1 ++ xs2 ++ [vtp])    

term2fgg g (TmCase tm (y, [], []) cs tp) =
  term2fgg g tm +>= \ xs ->
  let fvs = freeVars cs in
    bindCases (Map.toList (Map.union (freeVars tm) fvs)) (map (caseRule g fvs xs tm y cs tp) cs)

term2fgg _ (TmCase _ _ _ _) = error "Cannot compile polymorphic code"

-- fail (i.e., amb with no arguments) doesn't generate any rules, but
-- should still generate the left-hand side nonterminal
term2fgg g (TmAmb [] tp) = addNonterm (ElNonterminal (TmAmb [] tp)) [tp]
term2fgg g (TmAmb tms tp) =
  let fvs = Map.unions (map freeVars tms) in
    bindCases (Map.toList fvs) (map (uncurry $ ambRule g fvs tms tp) (collectDups tms))
    
term2fgg g (TmFactor wt tm tp) =
  term2fgg g tm +>= \ xs ->
  let vtp = (NnOut, tp)
      el = ElTerminal ("factor " ++ show wt) in
  addFactor el (Scalar wt) +>
  mkRule (TmFactor wt tm tp) (vtp : xs)
    [Edge [] el,
     Edge (xs ++ [vtp]) (ElNonterminal tm)]
    (xs ++ [vtp])
  
term2fgg g (TmLet x xtm xtp tm tp) =
  term2fgg g xtm +>= \ xtmxs ->
  bindExt x xtp $
  term2fgg (ctxtDefLocal g x xtp) tm +>= \ tmxs ->
  let vxtp = (NnVar x, xtp)
      vtp = (NnOut, tp) in -- TODO: if unused?
    mkRule (TmLet x xtm xtp tm tp) (vxtp : vtp : xtmxs ++ tmxs)
      [Edge (xtmxs ++ [vxtp]) (ElNonterminal xtm),
       Edge (tmxs ++ [vtp]) (ElNonterminal tm)]
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
      vptp = (NnOut, ptp)
      vtps = newNodeNames tps
  in
    addProdFactors g tps +>
    mkRule (TmProd am as) (vptp : vtps ++ concat xss)
      (Edge (vtps ++ [vptp]) (ElTerminal (prodFactorName (snds as))) :
        [Edge (tmxs ++ [vtp]) (ElNonterminal atm) | ((atm, atp), vtp, tmxs) <- zip3 as vtps xss])
      (concat xss ++ [vptp])

term2fgg g (TmElimProd Additive ptm ps tm tp) =
  term2fgg g ptm +>= \ ptmxs ->
  let o = injIndex [x | (x, _) <- ps]
      (x, xtp) = ps !! o in
    bindExt x xtp $
    term2fgg (ctxtDefLocal g x xtp) tm +>= \ tmxs ->
    let x' = NnVar x
        tps = snds ps
        ptp = TpProd Additive tps
        vtp = (NnOut, tp)
        [vptp] = newNodeNames [ptp]
    in
      addAmpFactors g tps +>
      mkRule (TmElimProd Additive ptm ps tm tp)
        (vtp : vptp : (x', xtp) : tmxs ++ ptmxs)
        [Edge (ptmxs ++ [vptp]) (ElNonterminal ptm),
         Edge (tmxs ++ [vtp]) (ElNonterminal tm),
         Edge [vptp, (x', xtp)] (ElTerminal (ampFactorName tps o))]
        (ptmxs ++ delete (x', xtp) tmxs ++ [vtp])

term2fgg g (TmElimProd Multiplicative ptm ps tm tp) =
  term2fgg g ptm +>= \ ptmxs ->
  bindExts ps $
  term2fgg (ctxtDeclArgs g ps) tm +>= \ tmxs ->
  let ps' = paramsToExternals ps
      tps = snds ps
      ptp = TpProd Multiplicative tps
      unused_ps = unusedExternals ps' tmxs
      vtp = (NnOut, tp)
      [vptp] = newNodeNames [ptp]
  in
    addProdFactors g tps +>
    mkRule (TmElimProd Multiplicative ptm ps tm tp)
      (vtp : vptp : ps' ++ unused_ps ++ tmxs ++ ptmxs)
      [Edge (ptmxs ++ [vptp]) (ElNonterminal ptm),
       Edge (ps' ++ [vptp]) (ElTerminal (prodFactorName tps)),
       Edge (tmxs ++ [vtp]) (ElNonterminal tm)]
         (ptmxs ++ foldr delete tmxs ps' ++ [vtp])

term2fgg g (TmEqs tms) =
  [term2fgg g tm | tm <- tms] +>=* \ xss ->
  let tmstp = typeof (head tms)
      ntms = length tms
      fac = ElTerminal (eqFactorName tmstp ntms)
      vbtp = (NnOut, tpBool)
      vtps = newNodeNames [typeof tm | tm <- tms] in
    addFactor fac (getEqWeights (domainSize g tmstp) ntms) +>
    mkRule (TmEqs tms)
      (vbtp : vtps ++ concat xss)
      (Edge (vtps ++ [vbtp]) fac : [Edge (xs ++ [vtp]) (ElNonterminal tm) | (tm, vtp, xs) <- zip3 tms vtps xss])
      (concat xss ++ [vbtp])

{- type2fgg g tp

   Adds factors for each subexpression in a type. -}

type2fgg :: Ctxt -> Type -> RuleM
type2fgg g tp =
  addFactor (ElTerminal (typeFactorName tp)) (getIdWeights (domainSize g tp)) +>
  type2fgg' g tp
  where
    type2fgg' :: Ctxt -> Type -> RuleM
    type2fgg' g (TpData y [] []) = returnRule
    type2fgg' g (TpArr tp1 tp2) = type2fgg g tp1 +> type2fgg g tp2
    type2fgg' g (TpProd am tps) = foldr (\ tp r -> r +> type2fgg g tp) returnRule tps
    type2fgg' g tp = error ("Compiling a " ++ show tp ++ " to FGG rule")

{- prog2fgg g prog

   Adds the rules for a Prog. -}
    
prog2fgg :: Ctxt -> Prog -> RuleM
prog2fgg g (ProgFun x ps tm tp) = let tp' = joinArrows (snds ps) tp in
  type2fgg g tp' +>= \ _ ->
  bindExts ps $ term2fgg (ctxtDeclArgs g ps) tm +>= \ tmxs ->
  let ps' = paramsToExternals ps
      unused_ps = unusedExternals ps' tmxs
      (unused_x, unused_tp) = unzip unused_ps
      vtp = (NnOut, tp)
  in
    mkRule (TmVarG DefVar x [] [] [] tp') (vtp : tmxs ++ ps' ++ unused_ps)
      (Edge (tmxs ++ [vtp]) (ElNonterminal tm) : [])
      (ps' ++ [vtp])
prog2fgg g (ProgExtern x ps tp) =
  let tp' = (joinArrows ps tp) in
    type2fgg g tp' +>
    addIncompleteFactor (ElNonterminal (TmVarG DefVar x [] [] [] tp'))
prog2fgg g (ProgData y cs) =
  -- Add constructor rules
  foldr (\ (Ctor x as) r -> r +> ctorRules g (Ctor x as) (TpData y [] []) cs) returnRule cs +>
  type2fgg g (TpData y [] [])

-- Goes through a program and adds all the rules for it
progs2fgg :: Ctxt -> Progs -> RuleM
progs2fgg g (Progs ps tm) =
  foldr (\ p rm -> rm +> prog2fgg g p) (term2fgg g tm) ps
  
{- domainValues g tp

   Computes a list of all the possible inhabitants of a type. -}

-- TODO: Instead list out the inhabitants as Terms, then show them

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
    [prodValName tmvs | tmvs <- kronall [tpVals tp | tp <- tps]]
  tpVals tp = error ("Enumerating values of a " ++ show tp)

domainSize :: Ctxt -> Type -> Int
domainSize g = length . domainValues g

{- compileFile progs

   Converts an elaborated program into an FGG (or returns an error). -}

compileFile :: Progs -> Either String FGG
compileFile ps =
  let g = ctxtDefProgs ps
      Progs _ end = ps
      RuleM rs xs nts fs = progs2fgg g ps
  in
      return (rulesToFGG (domainValues g) (ElNonterminal end) (reverse rs) nts fs)
