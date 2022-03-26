{-
Code that applies the following transformations:
1. define foo = \ a. \ b. tm;   =>   define foo a b = tm;
2. TmApp (TmApp (TmVarG x) tm1) tm2   =>   TmVarG x [tm1, tm2]
-}

module Nicify where
import qualified Data.Map as Map
import Exprs
import Util
import Name
import Subst


nicify :: Term -> Term
nicify (TmVarL x tp) = TmVarL x tp
nicify (TmVarG g x [] [] tp) =
  let (tps, etp) = splitArrows tp
      lxs = runSubst (Map.singleton x (SubVar x)) (freshens ["x" ++ show i | i <- [0..length tps - 1]])
      ls = zip lxs tps in
  joinLams ls (TmVarG g x [] (paramsToArgs ls) etp)
nicify (TmVarG g x tis as tp) = error (show (TmVarG g x tis as tp))
nicify (TmLam x xtp tm tp) = TmLam x xtp (nicify tm) tp
nicify tm@(TmApp _ _ _ _) =
  case splitApps tm of
    (TmVarG g x [] [] tp , as) ->
      let as' = [(nicify tm, tp) | (tm, tp) <- as]
          (tps, etp) = splitArrows tp
          remtps = drop (length as') tps
          tmfvs = Map.mapWithKey (const . SubVar) (freeVars tm)
          lxs = runSubst tmfvs (freshens ["x" ++ show i | i <- [0..length remtps - 1]])
          ls = zip lxs remtps
          as'' = as' ++ [(TmVarL x tp, tp) | (x, tp) <- ls]
      in
        joinLams ls (TmVarG g x [] as'' etp)
    (TmVarG g x tis as' tp, as) ->
      error (show (TmVarG g x tis as' tp))
    (etm, as) ->
      joinApps etm [(nicify tm, tp) | (tm, tp) <- as]
nicify (TmLet x xtm xtp tm tp) = TmLet x (nicify xtm) xtp (nicify tm) tp
nicify (TmCase tm y cs tp) = TmCase (nicify tm) y (fmap (\ (Case x ps tm') -> Case x ps (nicify tm')) cs) tp
nicify (TmSamp d tp) = TmSamp d tp
nicify (TmAmb tms tp) = TmAmb (nicify <$> tms) tp
nicify (TmProd am as) = TmProd am [(nicify tm, tp) | (tm, tp) <- as]
nicify (TmElimProd am ptm ps tm tp) = TmElimProd am (nicify ptm) ps (nicify tm) tp
nicify (TmEqs tms) = TmEqs (nicify <$> tms)

nicifyProg :: Prog -> Prog
nicifyProg (ProgFun x [] tm tp) =
  let tm' = nicify tm
      (as, etp) = splitArrows tp
      (ls, etm) = splitLams tm'
      etas = [ (etaName x i, atp) | (i, atp) <- drop (length ls) (enumerate as) ]
      etm_eta = joinApps etm (paramsToArgs etas)
      ls_eta = ls ++ etas
  in
    ProgFun x ls_eta etm_eta etp
nicifyProg (ProgExtern x [] tp) =
  let (tps, etp) = splitArrows tp in
    ProgExtern x tps etp
nicifyProg (ProgData y cs) = ProgData y cs
nicifyProg _ = error "This shouldn't happen"

nicifyFile :: Progs -> Progs
nicifyFile (Progs ps tm) = Progs (map nicifyProg ps) (nicify tm)
