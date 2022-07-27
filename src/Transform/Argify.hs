{-
Code that applies the following transformations:
1. define foo = \ a. \ b. tm;   =>   define foo a b = tm;
2. TmApp (TmApp (TmVarG x) tm1) tm2...   =>   TmVarG x [tm1, tm2, ...]

This transformation makes AffLin more efficient,
because we don't need to have functions like a -> b -> c
become (a -> ((b -> c) & Unit)) & Unit, only (a -> b -> c) & Unit
-}

module Transform.Argify where
import qualified Data.Map as Map
import Struct.Lib
import Util.Helpers
import Scope.Name
import Scope.Subst


argify :: Term -> Term
argify (TmVarL x tp) = TmVarL x tp
argify (TmVarG g x [] [] tp) =
  let (tps, etp) = splitArrows tp
      lxs = runSubst (Map.singleton x (SubVar x)) (freshens ["x" ++ show i | i <- [0..length tps - 1]])
      ls = zip lxs tps in
  joinLams ls (TmVarG g x [] (paramsToArgs ls) etp)
argify (TmVarG g x tis as tp) = error (show (TmVarG g x tis as tp))
argify (TmLam x xtp tm tp) = TmLam x xtp (argify tm) tp
argify tm@(TmApp _ _ _ _) =
  case splitApps tm of
    (TmVarG g x [] [] tp , as) ->
      let as' = [(argify tm, tp) | (tm, tp) <- as]
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
      joinApps etm [(argify tm, tp) | (tm, tp) <- as]
argify (TmLet x xtm xtp tm tp) = TmLet x (argify xtm) xtp (argify tm) tp
argify (TmCase tm y cs tp) = TmCase (argify tm) y (fmap (\ (Case x ps tm') -> Case x ps (argify tm')) cs) tp
argify (TmAmb tms tp) = TmAmb (argify <$> tms) tp
argify (TmFactor wt tm tp) = TmFactor wt (argify tm) tp
argify (TmProd am as) = TmProd am [(argify tm, tp) | (tm, tp) <- as]
argify (TmElimProd am ptm ps tm tp) = TmElimProd am (argify ptm) ps (argify tm) tp
argify (TmEqs tms) = TmEqs (argify <$> tms)

argifyProg :: Prog -> Prog
argifyProg (ProgFun x [] tm tp) =
  let tm' = argify tm
      (as, etp) = splitArrows tp
      (ls, etm) = splitLams tm'
      etas = [ (etaName x i, atp) | (i, atp) <- drop (length ls) (enumerate as) ]
      etm_eta = joinApps etm (paramsToArgs etas)
      ls_eta = ls ++ etas
  in
    ProgFun x ls_eta etm_eta etp
argifyProg (ProgExtern x tp) = ProgExtern x tp
argifyProg (ProgData y cs) = ProgData y cs
argifyProg tp = error $ "This shouldn't happen (" ++ show tp ++ ")"

argifyFile :: Progs -> Progs
argifyFile (Progs ps tm) = Progs (map argifyProg ps) (argify tm)
