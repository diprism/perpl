module Compile.Compile (compileFile) where
import Data.List
import qualified Data.Map as Map
import Compile.RuleM
import Util.Tensor (TensorLike)
import Util.FGG
import Util.Helpers
import Struct.Lib
import Scope.Ctxt (Ctxt, ctxtAddProgs, ctxtAddArgs, ctxtAddLocal, ctxtLookupType)
import Scope.Subst (FreeTmVars, freeVarLs)

newNodeNames :: [a] -> [(NodeName, a)]
newNodeNames as = [(NnInternal j, atp) | (j, atp) <- enumerate as]

paramsToNodes :: [Param] -> [Node]
paramsToNodes ps = [(NnVar x, tp) | (x, tp) <- ps]

unusedNodes :: [Node] -> [Node] -> [Node]
unusedNodes = deleteFirstsBy (\ (x1, _) (x2, _) -> x1 == x2)


{- bindCases xs rms

   Runs all of rms and keeps only the external nodes in xs. -}
                          
bindCases :: [Param] -> EdgeLabel -> [RuleM HGF] -> RuleM [Node]
bindCases xs lhs rms =
  sequence rms >>= addRuleBlock lhs >>
  return (paramsToNodes xs)

{- mkRule lhs ns es xs

Creates a rule.

- lhs: the left-hand side
- ns:  the right-hand side node ids and labels
- es:  the right-hand side edges
- xs:  the external node ids and labels -}

mkRule :: Term -> [Node] -> [Edge] -> [Node] -> RuleM [Node]
mkRule lhs ns es xs =
  let xs' = nub xs in
    addRuleBlock (ElNonterminal lhs) [HGF (nub ns) es xs'] >> return (init xs')

-- Add a rule for this particular case in a case-of statement
caseRule :: Ctxt -> FreeTmVars -> [Node] -> Term -> TpName -> Type -> Case -> RuleM HGF
caseRule g all_fvs xs_ctm ctm y tp (Case x as xtm) =
  term2fgg (ctxtAddArgs g as) xtm >>= \ xs_xtm_as ->
  let all_xs = paramsToNodes (Map.toList all_fvs)
      unused_ps = unusedNodes all_xs xs_xtm_as
      [vctp] = newNodeNames [TpData y [] []]
      vtp = (NnOut, tp)
      Just ctors = ctxtLookupType g y
      Just ci = findIndex (\ (Ctor x' _) -> x' == x) ctors
      fac = ElTerminal (FaCtor ctors ci)
      as' = paramsToNodes as
  in
    return (HGF (nub (vctp : vtp : xs_xtm_as ++ as' ++ xs_ctm ++ all_xs ++ unused_ps))
                [Edge (xs_ctm ++ [vctp]) (ElNonterminal ctm),
                 Edge (xs_xtm_as ++ [vtp]) (ElNonterminal xtm),
                 Edge (as' ++ [vctp]) fac]
                (nub (xs_ctm ++ all_xs ++ [vtp])))

-- Adds rule for the i-th term in an amb tm1 tm2 ... tmn
ambRule :: Ctxt -> FreeTmVars -> Type -> Term -> RuleM HGF
ambRule g all_fvs tp tm =
  term2fgg g tm >>= \ tmxs ->
  let all_xs = paramsToNodes (Map.toList all_fvs)
      unused_tms = unusedNodes all_xs tmxs
      vtp = (NnOut, tp)
  in
    return (HGF (nub (vtp : tmxs ++ all_xs ++ unused_tms))
                [Edge (tmxs ++ [vtp]) (ElNonterminal tm)]
                (nub (all_xs ++ [vtp])))

-- Adds rule for the i-th component of an &-product
ampRule :: Ctxt -> FreeTmVars -> [Arg] -> Int -> Term -> Type -> RuleM HGF
ampRule g all_fvs as i tm tp =
  term2fgg g tm >>= \ tmxs ->
  let tps = snds as
      all_xs = paramsToNodes (Map.toList all_fvs)
      unused_tms = unusedNodes all_xs tmxs
      [vamp] = newNodeNames [TpProd Additive tps]
      vtp = (NnOut, tp)
  in
    return (HGF (nub (vamp : vtp : tmxs ++ all_xs ++ unused_tms))
                [Edge (tmxs ++ [vtp]) (ElNonterminal tm),
                 Edge [vtp, vamp] (ElTerminal (FaAddProd tps i))]
                (nub (all_xs ++ [vamp])))

{- term2fgg g tm

   Traverse a term tm and add rules for it and all its subexpressions.

   Returns: A RuleM containing the rules, with an external node
   for each free variable in tm. -}

term2fgg :: Ctxt -> Term -> RuleM [Node]

-- Local variables:
--   (v0)-[x]-(v1) -> (v0)-[v0=v1]-(v1)
term2fgg g (TmVarL x tp) =
  let ns = [(NnVar x, tp), (NnOut, tp)] in
    mkRule (TmVarL x tp) ns [Edge ns (ElTerminal (FaIdentity tp))] ns

term2fgg g (TmVarG GlDefine x [] [] [] tp) =
  return [] -- If this is a def with no args, we already add its rule when it gets defined
  
term2fgg g (TmVarG GlExtern x [] [] as tp) =
  return [] -- Rule will be supplied externally

term2fgg g (TmVarG gv x [] [] as tp) =
  mapM (\ (a, atp) -> term2fgg g a) as >>= \ xss ->
  let ps = newNodeNames (snds as)
      vy = (NnOut, tp)
      el = case gv of GlDefine ->
                        ElNonterminal (TmVarG gv x [] [] [] (joinArrows (snds as) tp))
                      GlCtor ->
                        let (TpData y [] []) = tp
                            Just cs = ctxtLookupType g y
                            Just ci = findIndex (\ (Ctor x' _) -> x' == x) cs in
                          ElTerminal (FaCtor cs ci)
                      --GlExtern -> error "Impossible case"
  in
    mkRule (TmVarG gv x [] [] as tp) (vy : ps ++ concat xss)
      (Edge (ps ++ [vy]) el :
        [Edge (xs ++ [vtp]) (ElNonterminal atm) | (xs, (atm, atp), vtp) <- zip3 xss as ps])
      (concat xss ++ [vy])

term2fgg _ (TmVarG _ _ _ _ _ _) = error "Cannot compile polymorphic code"

term2fgg g (TmLam x tp tm tp') =
  term2fgg (ctxtAddLocal g x tp) tm >>= \ tmxs ->
   let [vtp'] = newNodeNames [tp']
       varr = (NnOut, TpArr tp tp')
       vtp = (NnVar x, tp) in
     mkRule (TmLam x tp tm tp') (vtp : vtp' : varr : tmxs)
       [Edge (tmxs ++ [vtp']) (ElNonterminal tm),
        Edge [vtp, vtp', varr] (ElTerminal (FaArrow tp tp'))]
       (delete vtp tmxs ++ [varr])

term2fgg g (TmApp tm1 tm2 tp2 tp) =
  term2fgg g tm1 >>= \ xs1 ->
  term2fgg g tm2 >>= \ xs2 ->
  let fac = ElTerminal (FaArrow tp2 tp)
      vtp = (NnOut, tp)
      [vtp2, varr] = newNodeNames [tp2, TpArr tp2 tp] in
    mkRule (TmApp tm1 tm2 tp2 tp) (vtp2 : vtp : varr : xs1 ++ xs2)
      [Edge (xs2 ++ [vtp2]) (ElNonterminal tm2),
       Edge (xs1 ++ [varr]) (ElNonterminal tm1),
       Edge [vtp2, vtp, varr] fac]
      (xs1 ++ xs2 ++ [vtp])    

term2fgg g (TmCase tm (y, [], []) cs tp) =
  term2fgg g tm >>= \ xs ->
  let fvs = freeVarLs cs in
    bindCases (Map.toList (Map.union (freeVarLs tm) fvs))
              (ElNonterminal (TmCase tm (y, [], []) cs tp))
              (map (caseRule g fvs xs tm y tp) cs) >>= \ xs' ->
    return (nub (xs ++ xs'))

term2fgg _ (TmCase _ _ _ _) = error "Cannot compile polymorphic code"

term2fgg g (TmAmb tms tp) =
  let fvs = Map.unions (map freeVarLs tms) in
    bindCases (Map.toList fvs)
              (ElNonterminal (TmAmb tms tp))
              (map (ambRule g fvs tp) tms)
    
term2fgg g (TmFactorDouble wt tm tp) =
  term2fgg g tm >>= \ xs ->
  let vtp = (NnOut, tp)
      el = ElTerminal (FaScalar wt) in
  mkRule (TmFactorDouble wt tm tp) (vtp : xs)
    [Edge [] el,
     Edge (xs ++ [vtp]) (ElNonterminal tm)]
    (xs ++ [vtp])

term2fgg g (TmFactorNat wt tm tp) =
  term2fgg g tm >>= \ xs ->
  let vtp = (NnOut, tp)
      el = ElTerminal (FaScalar (fromIntegral wt)) in
  mkRule (TmFactorNat wt tm tp) (vtp : xs)
    [Edge [] el,
     Edge (xs ++ [vtp]) (ElNonterminal tm)]
    (xs ++ [vtp])

term2fgg g (TmFactorRatio wt tm tp) =
  term2fgg g tm >>= \ xs ->
  let vtp = (NnOut, tp)
      el = ElTerminal (FaScalar (fromRational wt)) in
  mkRule (TmFactorRatio wt tm tp) (vtp : xs)
    [Edge [] el,
     Edge (xs ++ [vtp]) (ElNonterminal tm)]
    (xs ++ [vtp])

term2fgg g (TmLet x xtm xtp tm tp) =
  term2fgg g xtm >>= \ xtmxs ->
  term2fgg (ctxtAddLocal g x xtp) tm >>= \ tmxs ->
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
      fvs = freeVarLs tms in
    bindCases (Map.toList fvs)
              (ElNonterminal (TmProd Additive as))
              [ampRule g fvs as i atm tp | (i, (atm, tp)) <- enumerate as]
    
term2fgg g (TmProd am@Multiplicative as) =
  mapM (\ (a, atp) -> term2fgg g a) as >>= \ xss ->
  let tps = snds as
      ptp = TpProd am tps
      vptp = (NnOut, ptp)
      vtps = newNodeNames tps
  in
    mkRule (TmProd am as) (vptp : vtps ++ concat xss)
      (Edge (vtps ++ [vptp]) (ElTerminal (FaMulProd (snds as))) :
        [Edge (tmxs ++ [vtp]) (ElNonterminal atm) | ((atm, atp), vtp, tmxs) <- zip3 as vtps xss])
      (concat xss ++ [vptp])

term2fgg g (TmElimAdditive ptm n o (x, xtp) tm tp) =
  term2fgg g ptm >>= \ ptmxs ->
  term2fgg (ctxtAddLocal g x xtp) tm >>= \ tmxs ->
  let x' = NnVar x
      ptp@(TpProd Additive tps) = typeof ptm
      vtp = (NnOut, tp)
      [vptp] = newNodeNames [ptp]
  in
    mkRule (TmElimAdditive ptm n o (x, xtp) tm tp)
      (vtp : vptp : (x', xtp) : tmxs ++ ptmxs)
      [Edge (ptmxs ++ [vptp]) (ElNonterminal ptm),
       Edge (tmxs ++ [vtp]) (ElNonterminal tm),
       Edge [(x', xtp), vptp] (ElTerminal (FaAddProd tps o))]
      (ptmxs ++ delete (x', xtp) tmxs ++ [vtp])

term2fgg g (TmElimMultiplicative ptm ps tm tp) =
  term2fgg g ptm >>= \ ptmxs ->
  term2fgg (ctxtAddArgs g ps) tm >>= \ tmxs ->
  let ps' = paramsToNodes ps
      tps = snds ps
      ptp = TpProd Multiplicative tps
      unused_ps = unusedNodes ps' tmxs
      vtp = (NnOut, tp)
      [vptp] = newNodeNames [ptp]
  in
    mkRule (TmElimMultiplicative ptm ps tm tp)
      (vtp : vptp : ps' ++ unused_ps ++ tmxs ++ ptmxs)
      [Edge (ptmxs ++ [vptp]) (ElNonterminal ptm),
       Edge (ps' ++ [vptp]) (ElTerminal (FaMulProd tps)),
       Edge (tmxs ++ [vtp]) (ElNonterminal tm)]
         (ptmxs ++ foldr delete tmxs ps' ++ [vtp])

term2fgg g (TmEqs tms) =
  mapM (term2fgg g) tms >>= \ xss ->
  let tmstp = typeof (head tms)
      ntms = length tms
      fac = ElTerminal (FaEqual tmstp ntms)
      vbtp = (NnOut, tpBool)
      vtps = newNodeNames [typeof tm | tm <- tms] in
    mkRule (TmEqs tms)
      (vbtp : vtps ++ concat xss)
      (Edge (vtps ++ [vbtp]) fac : [Edge (xs ++ [vtp]) (ElNonterminal tm) | (tm, vtp, xs) <- zip3 tms vtps xss])
      (concat xss ++ [vbtp])

{- prog2fgg g prog

   Adds the rules for a Prog. -}
    
prog2fgg :: Ctxt -> Prog -> RuleM ()
prog2fgg g (ProgDefine x ps tm tp) = let tp' = joinArrows (snds ps) tp in
  term2fgg (ctxtAddArgs g ps) tm >>= \ tmxs ->
  let ps' = paramsToNodes ps
      unused_ps = unusedNodes ps' tmxs
      (unused_x, unused_tp) = unzip unused_ps
      vtp = (NnOut, tp)
  in
    mkRule (TmVarG GlDefine x [] [] [] tp') (vtp : tmxs ++ ps' ++ unused_ps)
      [Edge (tmxs ++ [vtp]) (ElNonterminal tm)]
      (ps' ++ [vtp]) >>
    return ()
prog2fgg g (ProgExtern x ps tp) = return ()
prog2fgg g (ProgData y cs) = return ()

-- Goes through a program and adds all the rules for it
progs2fgg :: Ctxt -> Progs -> RuleM ()
progs2fgg g (Progs ps tm) =
  mapM (prog2fgg g) ps >> term2fgg g tm >> return ()
  
{- domainValues g tp

   Computes the number and list of possible inhabitants of a type. -}

domain :: Ctxt -> Type -> Domain
domain g = tpDomain where

  tpDomain (TpData y [] []) =
    maybe2 (ctxtLookupType g y) (Domain 0 []) $ \ cs ->
    let dss :: [(TmName, [Domain])]
        dss = [ (x, map tpDomain as) | Ctor x as <- cs ]
        app :: Value -> Domain -> [Value]
        app (Value d) (Domain _ vals) = [ Value (d ++ " " ++ parens da)
                                        | Value da <- vals ]
    in Domain (sum    [ product [ sz | Domain sz _ <- ds ] | (x, ds) <- dss ])
              (concat [ foldlM app [Value (show x)] ds     | (x, ds) <- dss ])

  tpDomain tpArr@(TpArr _ _) =
    let (tps, tp) = splitArrows tpArr
        ds = map tpDomain tps
        Domain szRes valsRes = tpDomain tp
        lam :: Domain -> [String] -> [String]
        lam (Domain _ args) vals = [ d ++ " -> " ++ da | Value d <- args, da <- vals ]
    in Domain (product [ sz | Domain sz _ <- ds ] * szRes)
              (map (Value . parensIf (not $ null tps)) $
               foldr lam [ da | Value da <- valsRes ] ds)

  tpDomain (TpProd Additive tps) =
    let ds = map tpDomain tps
        add :: (Int, Domain) -> [Value]
        add (i, Domain _ vs) = [ Value ("<" ++ intercalate ", " [ if i == j then tmv else "_"
                                                                | (j, tp) <- enumerate tps ]
                                            ++ ">")
                               | Value tmv <- vs ]
    in Domain (sum [ sz | Domain sz _ <- ds ])
              (concatMap add (enumerate ds))

  tpDomain (TpProd Multiplicative tps) =
    let ds = map tpDomain tps
    in Domain (product [ sz | Domain sz _ <- ds ])
              [ Value ("(" ++ intercalate ", " [ v | Value v <- tmvs ] ++ ")")
              | tmvs <- kronall [ vals | Domain _ vals <- ds ] ]

  tpDomain tp = error ("Enumerating values of a " ++ show tp)

{- compileFile progs

   Converts an elaborated program into an FGG (or returns an error).

   Assumes that all local variables have unique names. If two local
   variables had the same name `x` but two different types, this would
   generate two FGG rules with lhs `x` that have external nodes with
   differently-shaped weights. -}

compileFile :: TensorLike tensor => Progs -> Either String (FGG tensor)
compileFile ps =
  let g = ctxtAddProgs ps
      Progs _ end = ps
      rs = runRuleM (progs2fgg g ps)
  in
      return (rulesToFGG (domain g) (ElNonterminal end) [typeof end] rs)
