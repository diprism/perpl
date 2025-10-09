{-
Applies the following transformations:
1. ProgDefine f [] (TmLam x (... tm)) (TpArr xtp (... tp))   =>   ProgDefine f [(x,xtp), ...] tm tp
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
import Scope.Name (localName)
import Scope.Fresh (newVars)
import Util.Helpers

argifyFile :: Progs -> Progs
argifyFile (Progs ps tm) = Progs (map argifyProg ps) (argifyTerm tm) where

  -- Find the argument and return types of every global function.
  -- Only the number of top-level lambdas in the definition are
  -- considered. So define f = factor 2.0 in \x. ... is considered to
  -- have no arguments.
  
  arity :: Prog -> [(TmName, ([Type], Type))]
  arity (ProgDefine x [] tm tp) = let (ls, etm) = splitLams tm in [(x, (snds ls, typeof etm))]
  arity (ProgExtern x [] tp) = let (tps, etp) = splitArrows tp in [(x, (tps, etp))]
  arity (ProgData x cs) = [(y, (tps, TpData x [] [])) | Ctor y tps <- cs]
  arity prog = error ("arity received a definition that is already argified: " ++ show prog)

  arities = Map.fromList (concat (map arity ps))

  --- Argify a term.

  argifyTerm :: Term -> Term
  argifyTerm (TmVarL x tp) = TmVarL x tp
  argifyTerm (TmVarG g x [] [] [] _) = argifyAppG g x []
  argifyTerm tm@(TmVarG g x tgs tis as tp) = error ("argifyTerm received a term that is already argified: " ++ show tm)
  argifyTerm (TmLam x xtp tm tp) = TmLam x xtp (argifyTerm tm) tp
  argifyTerm tm@(TmApp _ _ _ _) =
    case splitApps tm of
      (TmVarG g x [] [] [] _, as) -> argifyAppG g x as
      f@(TmVarG g x tgs tis as' _, as) ->
        error ("argifyTerm received a term that is already argified: " ++ show f)
      (etm, as) ->
        joinApps (argifyTerm etm) [(argifyTerm tm, tp) | (tm, tp) <- as]
  argifyTerm (TmLet x xtm xtp tm tp) = TmLet x (argifyTerm xtm) xtp (argifyTerm tm) tp
  argifyTerm (TmCase tm y cs tp) = TmCase (argifyTerm tm) y (fmap (\ (Case x ps tm') -> Case x ps (argifyTerm tm')) cs) tp
  argifyTerm (TmAmb tms tp) = TmAmb (argifyTerm <$> tms) tp
  argifyTerm (TmFactorDouble wt tm tp) = TmFactorDouble wt (argifyTerm tm) tp
  argifyTerm (TmFactorNat wt tm tp) = TmFactorNat wt (argifyTerm tm) tp
  argifyTerm (TmFactorRatio wt tm tp) = TmFactorRatio wt (argifyTerm tm) tp
  argifyTerm (TmProd am as) = TmProd am [(argifyTerm tm, tp) | (tm, tp) <- as]
  argifyTerm (TmElimMultiplicative ptm ps    tm tp) = TmElimMultiplicative (argifyTerm ptm) ps    (argifyTerm tm) tp
  argifyTerm (TmElimAdditive       ptm n i p tm tp) = TmElimAdditive       (argifyTerm ptm) n i p (argifyTerm tm) tp
  argifyTerm (TmEqs tms) = TmEqs (argifyTerm <$> tms)

  -- Argify an application of a global definition (TmVarG g x [] [] [] _)
  -- to zero or more arguments (as).
  argifyAppG :: Global -> TmName -> [Arg] -> Term
  argifyAppG g x as =
    -- as = the provided arguments
    -- tps = the argument types of x
    let as' = [(argifyTerm tm, tp) | (tm, tp) <- as]
        (tps, etp) = arities Map.! x
    in
      case drop (length as') tps of
        [] ->
          -- Absorb |tps| arguments into the TmVarG
          case splitAt (length tps) as' of
            (absorb, remain) -> joinApps (TmVarG g x [] [] absorb etp) remain
        remtps -> -- list of missing argument types
          -- This is a partial (or non-) application, so η-expand with the missing arguments.
          let
            lxs = newVars (replicate (length remtps) localName) (const False)
            ls = zip lxs remtps
            as'' = as' ++ paramsToArgs ls
          in
            joinLams ls (TmVarG g x [] [] as'' etp)

  -- Argify a definition.
  
  argifyProg :: Prog -> Prog
  argifyProg (ProgDefine x [] tm tp) =
    let (ls, etm) = splitLams tm
        etm' = argifyTerm etm
    in
      ProgDefine x ls etm' (typeof etm')
  argifyProg (ProgExtern x [] tp) =
    let (tps, etp) = splitArrows tp in
      ProgExtern x tps etp
  argifyProg (ProgData y cs) = ProgData y cs
  argifyProg _ = error "This shouldn't happen"

