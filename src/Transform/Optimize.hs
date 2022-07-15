module Transform.Optimize where
--import Data.Maybe
import qualified Data.Map as Map
import Struct.Lib
import Util.Helpers
import Scope.Name
import Scope.Free
import Scope.Subst
import Scope.Ctxt

{- Provides various optimizations:
1. (case t of C1 a* -> \x. t1 | C2 b* -> \y. t2 | C3 c* -> t3)
     -> (\x. case t of C1 a* -> t1 | C2 b* -> t2[y := x] | C3 c* -> t3 x)
2. (\ x. f) t   ->   (let x = t in f)
3. case-of-known-constructor
   (case C4 t* of C1 a* -> t1 | ... | C4 d* -> t4 | ...) -> (let d* = t* in t4)
4. (let x = t1 in t2) -> (t2[x := t1])     where x occurs once-ish in t2 (see note below)
5. (define y = \ a*. x a*; ...) -> ...[y := x]

Note that some of these have yet to be implemented

Notes:
- Optimization (1) enforces the invariant that the return type of every case-of is not
  an arrow type.

- Optimization (4) only happens when the let-bound variable occurs exactly once in its
  body, or when the let-definition has no global defs (excluding ctors), free local
  functions, or ambs/fails/uniforms in it. Consider if we did this unconditionally:
                      (let x = t1 in t2) -> (t2[x := t1]).
  This becomes problematic if, say, you have (let x = amb : Bool in t2) and t2 uses
  x twice because originally both uses of x were guaranteed to be the same, but when
  you substitute t2[x := amb : Bool], they become separated.
  It is also problematic if you remove unused let-definitions due to fail (and also
  amb, but fail is clearer). When you write (let x = fail : Bool in t2), the term
  will have weight 0 even if t2 does not use x. But when you substitute
  t2[x := fail : Bool], it's the same as the original t2, so no longer necessarily fails.

- Optimization (5) just gets rid of synonym definitions
-}

-- note: (case b of false -> x | true -> amb y z)
-- becomes
-- amb (case b of false ->    x | true -> fail)
--     (case b of false -> fail | true ->    y)
--     (case b of false -> fail | true ->    z)
-- This way it keeps the same probabilities:
-- p(result==x) = p(b==false)
-- p(result==y) = p(b==true)
-- p(result==z) = p(b==true)
liftAmb :: Term -> Term
liftAmb (TmVarL x tp) = TmVarL x tp
liftAmb (TmVarG gv x tis as tp) =
  let as' = [[(atm', atp) | atm' <- splitAmbs (liftAmb atm)] | (atm, atp) <- as] in
    joinAmbs [TmVarG gv x tis as tp | as <- (kronall as')] tp
liftAmb (TmLam x tp tm tp') =
  joinAmbs [TmLam x tp tm tp' | tm <- splitAmbs (liftAmb tm)] (TpArr tp tp') 
liftAmb (TmApp tm1 tm2 tp2 tp) =
  joinAmbs (kronwith (\ tm1' tm2' -> TmApp tm1' tm2' tp2 tp)
             (splitAmbs (liftAmb tm1))
             (splitAmbs (liftAmb tm2))) tp
liftAmb (TmLet x xtm xtp tm tp) =
  joinAmbs (kronwith (\ xtm' tm' -> TmLet x xtm' xtp tm' tp)
             (splitAmbs (liftAmb xtm))
             (splitAmbs (liftAmb tm))) tp
liftAmb (TmCase tm y cs tp) =
  let tms = splitAmbs (liftAmb tm)
      cs1 = [(x, xps, splitAmbs (liftAmb xtm)) | Case x xps xtm <- cs]
      cs2 = concatMap (\ (x, xps, xtms) -> [[Case x' xps' (if x == x' then xtm else TmAmb [] tp) | Case x' xps' _ <- cs] | xtm <- xtms]) cs1
      cs3 = if any (\ (x, xps, xtms) -> length xtms > 1) cs1 then cs2 else [cs]
  in
    joinAmbs (kronwith (\ tm cs -> TmCase tm y cs tp) tms cs3) tp
liftAmb (TmAmb tms tp) =
  TmAmb (concatMap (splitAmbs . liftAmb) tms) tp
liftAmb (TmFactor wt tm tp) =
  let tms = splitAmbs (liftAmb tm)
      tms' = [TmFactor wt atm tp | atm <- tms]
  in
    joinAmbs tms' tp
liftAmb (TmProd am as)
  | am == Multiplicative =
    let as' = [[(atm', atp) | atm' <- splitAmbs (liftAmb atm)] | (atm, atp) <- as] in
      joinAmbs (map (TmProd am) (kronall as')) (TpProd am (snds as))
  | otherwise = TmProd am (mapArgs liftAmb as)
{-liftAmb (TmElimProd Additive ptm ps tm tp) =
-- let <ps> = amb ptm in tm
  let pambs = splitAmbs (liftAmb ptm)
      tambs = splitAmbs (liftAmb tm) in    
    joinAmbs [TmElimProd Additive ptm o tp | tm <- splitAmbs (liftAmb tm)] tp
-}
liftAmb (TmElimProd am ptm ps tm tp) =
  joinAmbs (kronwith (\ ptm' tm' -> TmElimProd am ptm' ps tm' tp)
             (splitAmbs (liftAmb ptm))
             (splitAmbs (liftAmb tm))) tp
liftAmb (TmEqs tms) =
  let tms' = [splitAmbs (liftAmb tm) | tm <- tms] in
    joinAmbs (map TmEqs (kronall tms')) (TpVar "Bool" [])

liftFail'' :: (Term, Maybe Term) -> Term
liftFail'' (tm, Nothing) = TmAmb [] (typeof tm)
liftFail'' (tm, Just tm') = tm'

liftFail' :: Term -> Maybe Term
liftFail' (TmVarL x tp) = pure (TmVarL x tp)
liftFail' (TmVarG gv x tis as tp) =
  pure (TmVarG gv x tis) <*> mapArgsM liftFail' as <*> pure tp
liftFail' (TmLam x tp tm tp') = pure (TmLam x tp (liftFail tm) tp')
liftFail' (TmApp tm1 tm2 tp2 tp) = pure TmApp <*> liftFail' tm1 <*> liftFail' tm2 <*> pure tp2 <*> pure tp
liftFail' (TmLet x xtm xtp tm tp) =
  pure (TmLet x) <*> liftFail' xtm <*> pure xtp <*> liftFail' tm <*> pure tp
liftFail' (TmCase tm y cs tp) =
  let cs' = [pure (Case x ps) <*> liftFail' tm | Case x ps tm <- cs] in
    if all null cs' then Nothing else
      pure TmCase <*> liftFail' tm <*> pure y
        <*> pure [Case x xps (liftFail xtm) | Case x xps xtm <- cs] <*> pure tp
liftFail' (TmAmb tms tp) =
  let tms' = concatMap (maybe [] (\ tm -> [tm]) . liftFail') tms in
    if null tms' then Nothing else pure (joinAmbs tms' tp)
liftFail' (TmFactor wt tm tp) = pure (TmFactor wt) <*> liftFail' tm <*> pure tp
liftFail' (TmProd am as)
  | am == Multiplicative =
    pure (TmProd am) <*> mapArgsM liftFail' as
  | otherwise =
    let as' = map (mapArgM liftFail') as in
      pure (TmProd am [maybe (TmAmb [] tp, tp) id ma | ((_, tp), ma) <- zip as as'])
--liftFail' (TmElimAmp tm tps o) =
--  pure TmElimAmp <*> liftFail' tm <*> pure tps <*> pure o
liftFail' (TmElimProd am tm ps tm' tp) =
  pure (TmElimProd am) <*> liftFail' tm <*> pure ps <*> liftFail' tm' <*> pure tp
liftFail' (TmEqs tms) =
  pure TmEqs <*> mapM liftFail' tms

-- If a term inevitably fails, just replace it with fail.
-- For example, (sample fail : tp1 -> tp2) tm1 is the same
-- as just having sample fail : tp2
liftFail :: Term -> Term
liftFail tm = liftFail'' (tm, liftFail' tm)

-- TODO: implement these optimizations

-- Peels off the lams around a term and substitutes their bound variables for others
-- Example 1: peelLams g [(x, Bool)] (\ z : Bool. and true z) = (and true x)
-- Example 2: peelLams g [(x, Bool)] (and true) = (and true x)
peelLams :: Ctxt -> [Param] -> Term -> Term
peelLams g [] tm = tm
peelLams g ps tm =
  let (ls, body) = splitLams tm
      subs = zip (fsts ls) (map (SubTm . fst) (paramsToArgs ps))
      -- See examples above
      example1 = substWithCtxt g (Map.fromList subs) body
      example2 = joinApps example1 (paramsToArgs (drop (length ls) ps)) in
    example2

-- Returns whether or not it is safe to substitute a term into another
-- More specifically, returns true when there are no global vars (excluding ctors),
-- no free vars that aren't also free in the other term, and no effects
safe2sub :: Ctxt -> Var -> Term -> Term -> Bool
safe2sub g x xtm tm =
  isLin' x tm || (noDefsSamps xtm && fvsOkay (freeVars xtm))
  where
    fvsOkay :: FreeVars -> Bool
    -- TODO: don't need to check isInfiniteType g tp, once we can copy terms with recursive datatypes
    fvsOkay fvs = all (\ (_, tp) -> robust g tp) (Map.toList fvs)
    
    -- Returns if there are no global def vars or ambs/fails/uniforms
    noDefsSamps :: Term -> Bool
    noDefsSamps (TmVarL x tp) = True
    noDefsSamps (TmVarG g x _ as tp) = g == CtorVar && all (noDefsSamps . fst) as
    noDefsSamps (TmLam x tp tm tp') = noDefsSamps tm
    noDefsSamps (TmApp tm1 tm2 tp2 tp) = noDefsSamps tm1 && noDefsSamps tm2
    noDefsSamps (TmLet x xtm xtp tm tp) = noDefsSamps xtm && noDefsSamps tm
    noDefsSamps (TmCase tm y cs tp) = noDefsSamps tm && all (\ (Case x xps xtm) -> noDefsSamps xtm) cs
    noDefsSamps (TmAmb tms tp) = False
    noDefsSamps (TmFactor wt tm tp) = False
    noDefsSamps (TmProd am as) = all (noDefsSamps . fst) as
--    noDefsSamps (TmElimAmp tm tps o) = noDefsSamps tm
    noDefsSamps (TmElimProd am tm ps tm' tp) = noDefsSamps tm && noDefsSamps tm'
    noDefsSamps (TmEqs tms) = all noDefsSamps tms

-- Applies various optimizations to a term
optimizeTerm :: Ctxt -> Term -> Term
optimizeTerm g (TmVarL x tp) = TmVarL x tp
optimizeTerm g (TmVarG gv x tis as tp) =
  TmVarG gv x tis (optimizeArgs g as) tp
optimizeTerm g (TmLet x xtm xtp tm tp) =
  let xtm' = optimizeTerm g xtm
      tm' = optimizeTerm (ctxtDeclTerm g x xtp) tm in
  if safe2sub g x xtm' tm'
    then optimizeTerm g (substWithCtxt g (Map.fromList [(x, SubTm xtm')]) tm')
    else TmLet x xtm' xtp tm' tp
optimizeTerm g (TmFactor wt tm tp) = TmFactor wt (optimizeTerm g tm) tp
optimizeTerm g (TmLam x tp tm tp') =
  TmLam x tp (optimizeTerm (ctxtDeclTerm g x tp) tm) tp'
optimizeTerm g (TmApp tm1 tm2 tp2 tp) =
  let (body, as) = splitApps (TmApp tm1 tm2 tp2 tp)
      body1 = optimizeTerm g body
      as' = optimizeArgs g as
      (ds, body2) = splitLets body1
      (ls, body3) = splitLams body2
      lets = [(lx, atm, atp) | ((lx, ltp), (atm, atp)) <- zip ls as']
      rem_as = drop (length lets) as'
      rem_ls = drop (length lets) ls
      let_tm = joinLets (ds ++ lets) body3
      -- Either rem_as or rem_ls must be [], so just expand with both:
      rtm = joinLams rem_ls (joinApps let_tm rem_as)
  in
    if null lets then rtm else optimizeTerm g rtm
optimizeTerm g (TmCase tm y cs tp) =
  let tm' = optimizeTerm g tm in
    case splitLets tm' of
      (ds, TmVarG CtorVar x tis as _) ->
        let [Case _ cps ctm] = filter (\ (Case x' _ _) -> x == x') cs
            p_a_ds = zipWith (\ (tm, _) (x', tp) -> (x', tm, tp)) as cps in
          optimizeTerm g (joinLets (ds ++ p_a_ds) ctm)
      _ ->
        let (ps, end) = splitArrows tp
            g_ps = foldr (\ (Case x xps xtm) g -> ctxtDeclArgs g xps) g cs
            (_, _, rps') = foldl (\ (e, g', ps') p ->
                                    let e' = freshVar g' e in
                                      (e', ctxtDeclTerm g' e' p, (e', p) : ps'))
                           (etaName "e" 0, g_ps, []) ps
            ps' = reverse rps'
            cs' = [let g' = ctxtDeclArgs g (ps' ++ xps) in Case x xps (peelLams g' ps' (optimizeTerm g' xtm)) | Case x xps xtm <- cs]
        in
          joinLams ps' (TmCase tm' y cs' end)
optimizeTerm g (TmAmb tms tp) = TmAmb (map (optimizeTerm g) tms) tp
optimizeTerm g (TmProd am as) = TmProd am (mapArgs (optimizeTerm g) as)
optimizeTerm g (TmElimProd Additive ptm ps tm tp) =
  case optimizeTerm g ptm of
    (TmProd Additive as) -> optimizeTerm g (substWithCtxt g (Map.fromList [(x, SubTm tm) | ((x, _), (tm, _)) <- zip ps as]) tm)
    ptm' -> TmElimProd Additive ptm' ps (optimizeTerm (ctxtDeclArgs g ps) tm) tp
optimizeTerm g (TmElimProd Multiplicative tm ps tm' tp) =
  TmElimProd Multiplicative (optimizeTerm g tm) ps (optimizeTerm (ctxtDeclArgs g ps) tm') tp
optimizeTerm g (TmEqs tms) =
  TmEqs [optimizeTerm g tm | tm <- tms]

-- Applies various optimizations to a list of args
optimizeArgs :: Ctxt -> [Arg] -> [Arg]
optimizeArgs g as = [(optimizeTerm g atm, atp) | (atm, atp) <- as]

-- Applies the optimizations specified at the BOF to a program
optimizeFile :: Progs -> Either String Progs
optimizeFile ps =
  let g = ctxtDefProgs ps in
    mapProgsM (return . liftFail . optimizeTerm g . liftFail {- . liftAmb-}) ps
