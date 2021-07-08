module Compile where
import Data.List
import Exprs
import FGG
import Util
import RuleM
import Ctxt


-- TODO: rework ctor and internal factor weights to range over all
--       values of types; e.g. weights of Maybe Bool range over
--       {nothing [Bool], just [Bool] true, just [Bool] false}

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


-- Add rule for a term application
tmapp2fgg :: Ctxt -> Term -> RuleM
tmapp2fgg g (TmApp tm1 tm2 tp2 tp) =
  term2fgg g tm1 +>= \ xs1 ->
  term2fgg g tm2 +>= \ xs2 ->
  let fac = pairFactorName tp2 tp
      (ns, [[itp2, itp, iarr], ixs1, ixs2]) =
        combine [[tp2, tp, TpArr tp2 tp], map snd xs1, map snd xs2]
      es = [Edge (itp2 : ixs2) (show tm2),
            Edge (iarr : ixs1) (show tm1),
            Edge [itp2, itp, iarr] fac]
      xs = itp : ixs1 ++ ixs2 in
    addRule' (TmApp tm1 tm2 tp2 tp) ns es xs +>
    addFactor fac (getPairWeights tp2 tp)


-- Eta-expands a constructor and adds all necessary rules
{-
ctorEtaRule :: Ctor -> Var -> RuleM
ctorEtaRule (Ctor x []) y = returnRule -- if no args, no need to eta-expand
ctorEtaRule (Ctor x as) y =
  let eta = (ctorAddLams x (ctorGetArgs x as) (TpVar y)) in
  addRule' (TmVar x (joinArrows as (TpVar y)) ScopeCtor) [TpVar y] [Edge [0] (show eta)] [0]

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
      tm = ctorAddArgs x (zip as' as) y
      fac = ctorFactorName x (zip as' as)
      es = [Edge (ias ++ [iy]) fac]
      xs = ias ++ [iy] in
    addRule' tm ns es xs +>
    ctorEtaRule  (Ctor x as) y +>
    ctorLamRules (Ctor x as) y +>
    addFactor fac (getCtorWeights ix (length cs))
-}
-- Add rule for a constructor
ctorRules :: Ctor -> Var -> [Ctor] -> RuleM
ctorRules (Ctor x as) y cs =
  let ix = foldr (\ (Ctor x' _) next ix -> if x == x' then ix else next (ix + 1)) id cs 0
      as' = map (ctorEtaName x) [0..length as - 1]
      (ns, [ias, [iy]]) = combine [as, [TpVar y]]
      ias' = zip ias as'
      fac = ctorFactorName x (toTermArgs (zip as' as))
      es = [Edge (ias ++ [iy]) fac]
      xs = ias ++ [iy]
      tm = TmCtor x (map (\ (a, atp) -> (TmVar a atp ScopeLocal, atp)) (zip as' as)) y in
    addRule' tm ns es xs +>
    -- default, in case this ctor never gets called:
    addFactor fac (getCtorWeights ix (length cs))

ctorsRules :: [Ctor] -> Var -> RuleM
ctorsRules cs y =
 foldr (\ c r -> r +> ctorRules c y cs) returnRule cs

ctorsFactors :: [Ctor] -> Var -> RuleM
ctorsFactors cs y = addFactor (typeFactorName (TpVar y)) (getCtorEqWeights (length cs))

-- Add a rule for this particular case in a case-of statement
caseRule :: Ctxt -> [(Var, Type)] -> Term -> Case -> RuleM
caseRule g xs_ctm (TmCase ctm cs y tp) (Case x as xtm) =
  let g' = ctxtDeclArgs g as in
  bindExts True as (term2fgg g' xtm) +>= \ xs_xtm ->
  let fac = ctorFactorName x (toTermArgs (ctorGetArgs x (map snd as)))
      (ns, [[ictm, ixtm], ixs_as, ixs_ctm, ixs_xtm]) =
        combine [[TpVar y, tp], map snd as, map snd xs_ctm, map snd xs_xtm]
      es = [Edge (ictm : ixs_ctm) (show ctm),
            Edge (ixtm : ixs_xtm ++ ixs_as) (show xtm),
            Edge (ixs_as ++ [ictm]) fac]
      xs = ixtm : ixs_ctm ++ ixs_xtm in
    addRule' (TmCase ctm cs y tp) ns es xs
caseRule g xs _ (Case x as xtm) =
  error "caseRule expected a TmCase, but got something else"

-- Add a rule for a lambda term
lamRule :: Bool -> Var -> Type -> Term -> Type -> RuleM -> RuleM
lamRule addVarRule x tp tm tp' rm =
  bindExt addVarRule x tp rm +>= \ xs' ->
  let (ns, [[itp, itp', iarr], ixs']) = combine [[tp, tp', TpArr tp tp'], map snd xs']
      es = [Edge ([itp, itp'] ++ ixs') (show tm),
            Edge [itp, itp', iarr] (pairFactorName tp tp')]
      xs = iarr : ixs' in
    addRule' (TmLam x tp tm tp') ns es xs +>
    addFactor (pairFactorName tp tp') (getPairWeights tp tp')

-- Traverse a term and add all rules for subexpressions
term2fgg :: Ctxt -> Term -> RuleM
term2fgg g (TmVar x tp local) =
  case local of
    ScopeGlobal -> returnRule
    ScopeLocal -> addExt x tp
    ScopeCtor -> error ("term2fgg should not see a ctor var (" ++ x ++ ")")
term2fgg g (TmCtor x as y) =
  map (\ (a, atp) -> term2fgg g a) as +*>= \ xss ->
  let (ns, [iy] : ias : ixss) = combine ([TpVar y] : map snd as : map (map snd) xss)
      es = Edge (iy : ias) (show (TmCtor x as y)) : map (\ (ixs, (a, _), itp) -> Edge (itp : ixs) (show a)) (zip3 ixss as ias)
      xs = iy : concat ixss
      Just cs = ctxtLookupType g y
      cix = foldr (\ (Ctor x' _) next ix -> if x == x' then ix else next (ix + 1)) id cs 0 in
  addRule' (TmCtor x as y) ns es xs +>
  addFactor (ctorFactorName x as) (getCtorWeights cix (length cs))
term2fgg g (TmLam x tp tm tp') =
  lamRule True x tp tm tp' (term2fgg (ctxtDeclTerm g x tp) tm)
term2fgg g (TmApp tm1 tm2 tp2 tp) =
  tmapp2fgg g (TmApp tm1 tm2 tp2 tp)
term2fgg g (TmCase tm cs y tp) =
  term2fgg g tm +>= \ xs ->
  foldr (\ c r -> caseRule g xs (TmCase tm cs y tp) c +> r) returnRule cs
term2fgg g (TmSamp d tp) =
  let dvs = domainValues g tp
      dvws = WeightsDims $ WeightsData dvs in
  case d of
    DistFail -> returnRule
    DistUni  ->
      addFactor (show $ TmSamp d tp) (ThisWeight (fmap (const (1.0 / fromIntegral (length dvs))) dvws)) +>
      addRule' (TmSamp d tp) [tp] [] [0]
    DistAmb  -> 
      addFactor (show $ TmSamp d tp) (ThisWeight (fmap (const 1) dvws)) +>
      addRule' (TmSamp d tp) [tp] [] [0]
term2fgg g (TmMaybe Nothing tp) =
  let fac = maybeFactorName Nothing tp
      ws = 1 : map (const 0) (domainValues g tp) in
    addRule' (TmMaybe Nothing tp) [TpMaybe tp] [Edge [0] fac] [0] +>
    addFactor fac (ThisWeight $ WeightsDims $ WeightsData ws)
term2fgg g (TmMaybe (Just tm) tp) =
  term2fgg g tm +>= \ xs ->
  let fac = maybeFactorName (Just tm) tp
      (ns, [imtp : itp : ixs]) = combine [TpMaybe tp : tp : map snd xs]
      es = [Edge (ixs ++ [itp]) (show tm), Edge [itp, imtp] fac]
      ws = 0 : map (const 1) (domainValues g tp) in
    addRule' (TmMaybe (Just tm) tp) ns es ixs +>
    addFactor fac (ThisWeight $ WeightsDims $ WeightsData ws)
term2fgg g (TmElimMaybe tm xtp ntm (jx, jtm) vtp) =
  term2fgg g tm +>= \ tmxs ->
  term2fgg g ntm +>= \ ntmxs ->
  bindExt True jx xtp (term2fgg (ctxtDeclTerm g jx xtp) jtm) +>= \ jtmxs ->
  let (n_ns, [[n_iv, n_itm], n_itmxs, n_intmxs]) =
        combine [[vtp, TpMaybe xtp], map snd tmxs, map snd ntmxs]
      (j_ns, [[j_iv, j_ix, j_itm], j_itmxs, j_ijtmxs]) =
        combine [[vtp, xtp, TpMaybe xtp], map snd tmxs, map snd jtmxs]
      n_es = [Edge (n_itm : n_itmxs) (show tm),
              Edge (n_iv : n_intmxs) (show ntm),
              Edge [n_itm] (maybeFactorName Nothing xtp)]
      j_es = [Edge (j_itm : j_itmxs) (show tm),
              Edge (j_iv : j_ix : j_ijtmxs) (show jtm),
              Edge [j_itm, j_ix] (maybeFactorName (Just (TmVar jx xtp ScopeLocal)) xtp)]
      n_xs = n_itmxs ++ n_intmxs
      j_xs = j_itmxs ++ j_ijtmxs
  in
  addRule' (TmElimMaybe tm xtp ntm (jx, jtm) vtp) n_ns n_es n_xs +>
  addRule' (TmElimMaybe tm xtp ntm (jx, jtm) vtp) j_ns j_es j_xs
term2fgg g (TmBool b) =
  let fac = internalFactorName (TmBool b)
      ws = if b then [0, 1] else [1, 0] in
    addRule' (TmBool b) [TpBool] [Edge [0] fac] [0] +>
    addFactor fac (ThisWeight $ WeightsDims $ WeightsData ws)
term2fgg g (TmIf iftm thentm elsetm tp) =
  term2fgg g iftm +>= \ ifxs ->
  term2fgg g thentm +>= \ thenxs ->
  term2fgg g elsetm +>= \ elsexs ->
  let (t_ns, [[t_iv, t_iif], t_iifxs, t_ithenxs]) =
        combine [[tp, TpBool], map snd ifxs, map snd thenxs]
      (f_ns, [[f_iv, f_iif], f_iifxs, f_ielsexs]) =
        combine [[tp, TpBool], map snd ifxs, map snd elsexs]
      t_es = [Edge (t_iif : t_iifxs) (show iftm),
              Edge (t_iv : t_ithenxs) (show thentm),
              Edge [t_iif] (internalFactorName (TmBool True))]
      f_es = [Edge (f_iif : f_iifxs) (show iftm),
              Edge (f_iv : f_ielsexs) (show elsetm),
              Edge [f_iif] (internalFactorName (TmBool False))]
      t_xs = t_iifxs ++ t_ithenxs
      f_xs = f_iifxs ++ f_ielsexs
  in
  addRule' (TmIf iftm thentm elsetm tp) t_ns t_es t_xs +>
  addRule' (TmIf iftm thentm elsetm tp) f_ns f_es f_xs

-- Goes through a program and adds all the rules for it
prog2fgg :: Ctxt -> Progs -> RuleM
prog2fgg g (ProgExec tm) = term2fgg g tm
prog2fgg g (ProgFun x tp tm ps) =
  prog2fgg g ps +> term2fgg g tm +> addRule' (TmVar x tp ScopeGlobal) [tp] [Edge [0] (show tm)] [0]
prog2fgg g (ProgExtern x tp ps) =
  prog2fgg g ps +> addNonterm x tp
prog2fgg g (ProgData y cs ps) =
  prog2fgg g ps +> ctorsFactors cs y +> ctorsRules cs y

-- TODO: Name external nodes with lookup map

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
          [x] (map (domainValues g) as)
  tpVals (TpArr tp1 tp2) = uncurry arrVals (splitArrows (TpArr tp1 tp2))
  tpVals TpBool = [tmFalseName, tmTrueName]
  tpVals (TpMaybe tp) =
    tmNothingName : map (\ tp -> "(" ++ tmJustName ++ " " ++ tp ++ ")") (tpVals tp)

maybeFactorName :: Maybe Term -> Type -> String
maybeFactorName Nothing tp = internalFactorName (TmMaybe Nothing tp)
maybeFactorName (Just tm) tp = internalFactorName (TmMaybe (Just (TmVar "" tp ScopeLocal)) tp)

addInternalFactors :: RuleM
addInternalFactors =
  let boolCtors = [Ctor tmFalseName [], Ctor tmTrueName []]
--      maybeCtors = [Ctor tmNothingName [], Ctor tmJustName []]
  in
  ctorsFactors boolCtors tpBoolName +>
--  ctorsFactors maybeCtors tpMaybeName +>
  foldr (\ c rm -> ctorRules c tpBoolName boolCtors +> rm) returnRule boolCtors
--  foldr (\ c rm -> ctorRules c tpMaybeName maybeCtors +> rm) returnRule maybeCtors

-- Converts an elaborated program into an FGG
file2fgg :: Ctxt -> Progs -> FGG_JSON
file2fgg g ps =
  let RuleM rs xs nts fs = addInternalFactors +> prog2fgg g ps in
    rulesToFGG (domainValues g) (show $ getStartTerm ps) (reverse rs) nts fs
