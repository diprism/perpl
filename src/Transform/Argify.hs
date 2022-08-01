{-
Applies the following transformations:
1. ProgFun f [] (TmLam x (... tm)) (TpArr xtp (... tp))   =>   ProgFun f [(x,xtp), ...] tm tp
2. TmApp (TmApp (TmVarG x []) tm1) tm2...   =>   TmVarG x [tm1, tm2, ...]
   with partial applications η-expanded.

This transformation makes AffLin more efficient,
because we don't need to have functions like a -> b -> c
become (a -> ((b -> c) & Unit)) & Unit, only (a -> b -> c) & Unit

This also makes compilation to an FGG more efficient,
because the rule for a global function can take all its arguments at once.
-}

module Transform.Argify where
import qualified Data.Map as Map
import Struct.Lib
import Scope.Subst
import Util.Helpers

argifyFile :: Progs -> Progs
argifyFile (Progs ps tm) = Progs (map argifyProg ps) (argifyTerm tm) where

  -- Find the argument and return types of every global function.
  -- Only the number of top-level lambdas in the definition are
  -- considered. So define f = factor 2.0 in \x. ... is considered to
  -- have no arguments.
  
  arity :: Prog -> [(Var, ([Type], Type))]
  arity (ProgFun x [] tm tp) = let (ls, etm) = splitLams tm in [(x, (snds ls, typeof etm))]
  arity (ProgExtern x [] tp) = let (tps, etp) = splitArrows tp in [(x, (tps, etp))]
  arity (ProgData x cs) = [(y, (tps, TpData x [])) | Ctor y tps <- cs]
  arity _ = []

  arities = Map.fromList (concat (map arity ps))

  --- Argify a term.

  argifyTerm :: Term -> Term
  argifyTerm (TmVarL x tp) = TmVarL x tp
  argifyTerm (TmVarG g x [] [] tp) =
    -- No arguments were provided, so η-expand by the number of arguments of x
    let (tps, etp) = arities Map.! x
        lxs = runSubst (Map.singleton x (SubVar x)) (freshens ["x" ++ show i | i <- [0..length tps - 1]])
        ls = zip lxs tps
    in
      joinLams ls (TmVarG g x [] (paramsToArgs ls) etp)
  argifyTerm tm@(TmVarG g x tis as tp) = error ("argifyTerm received a term that is already argified: " ++ show tm)
  argifyTerm (TmLam x xtp tm tp) = TmLam x xtp (argifyTerm tm) tp
  argifyTerm tm@(TmApp _ _ _ _) =
    case splitApps tm of
      (TmVarG g x [] [] tp, as) ->
        -- as = the provided arguments
        -- tps = the argument types of x
        let as' = [(argifyTerm tm, tp) | (tm, tp) <- as]
            (tps, etp) = arities Map.! x
        in
          if length as' < length tps then
            -- This is a partial application, so η-expand with the missing arguments.
            let
              remtps = drop (length as') tps -- list of missing argument types
              tmfvs = Map.mapWithKey (const . SubVar) (freeVars tm)
              lxs = runSubst tmfvs (freshens ["x" ++ show i | i <- [0..length remtps - 1]])
              ls = zip lxs remtps
              as'' = as' ++ [(TmVarL x tp, tp) | (x, tp) <- ls]
            in
              joinLams ls (TmVarG g x [] as'' etp)
          else
            -- Absorb |tps| arguments into the TmVarG
            joinApps (TmVarG g x [] (take (length tps) as') etp) (drop (length tps) as')
      f@(TmVarG g x tis as' tp, as) ->
        error ("argifyTerm received a term that is already argified: " ++ show f)
      (etm, as) ->
        joinApps (argifyTerm etm) [(argifyTerm tm, tp) | (tm, tp) <- as]
  argifyTerm (TmLet x xtm xtp tm tp) = TmLet x (argifyTerm xtm) xtp (argifyTerm tm) tp
  argifyTerm (TmCase tm y cs tp) = TmCase (argifyTerm tm) y (fmap (\ (Case x ps tm') -> Case x ps (argifyTerm tm')) cs) tp
  argifyTerm (TmAmb tms tp) = TmAmb (argifyTerm <$> tms) tp
  argifyTerm (TmFactor wt tm tp) = TmFactor wt (argifyTerm tm) tp
  argifyTerm (TmProd am as) = TmProd am [(argifyTerm tm, tp) | (tm, tp) <- as]
  argifyTerm (TmElimProd am ptm ps tm tp) = TmElimProd am (argifyTerm ptm) ps (argifyTerm tm) tp
  argifyTerm (TmEqs tms) = TmEqs (argifyTerm <$> tms)

  -- Argify a definition.
  
  argifyProg :: Prog -> Prog
  argifyProg (ProgFun x [] tm tp) =
    let (ls, etm) = splitLams tm
        etm' = argifyTerm etm
    in
      ProgFun x ls etm' (typeof etm')
  argifyProg (ProgExtern x [] tp) =
    let (tps, etp) = splitArrows tp in
      ProgExtern x tps etp
  argifyProg (ProgData y cs) = ProgData y cs
  argifyProg _ = error "This shouldn't happen"

