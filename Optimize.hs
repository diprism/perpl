module Optimize where
import Data.List
import qualified Data.Map as Map
import Exprs
import Ctxt
import Util
import Name
import Rename
import Free

{- Provides various optimizations:
1. (case t of C1 a* -> \x. t1 | C2 b* -> \y. t2 | C3 c* -> t3)
     -> (\x. case t of C1 a* -> t1 | C2 b* -> t2[y := x] | C3 c* -> t3 x)
2. (\ x. f) t   ->   (let x = t in f)
3. (case C4 t* of C1 a* -> t1 | ... | C4 d* -> t4 | ...) -> (let d* = t* in t4)
4. (let x = t1 in t2) -> (t2[x := t1])     where x occurs once-ish in t2 (see note below)
5. (define y = \ a*. x a*; ...) -> ...[y := x]

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

-- TODO: implement these optimizations
-- TODO: Opts (1) & (2) should check for lets: ((let x = t1 in \y. t2) t3) -> (let x = t1 in t2[y := t3])    (maybe just push lets down as far as possible, stopping at case-ofs/vars?)

-- Peels off the lams around a term and substitutes their bound variables for others
-- Example 1: peelLams g [(x, Bool)] (\ z : Bool. and true z) = (and true x)
-- Example 2: peelLams g [(x, Bool)] (and true) = (and true x)
peelLams :: Ctxt -> [Param] -> Term -> Term
peelLams g [] tm = tm
peelLams g ps tm =
  let (ls, body) = splitLams tm
      subs = zip (map fst ls) (map (Left . fst) (paramsToArgs ps))
      -- See examples above
      example1 = substs g subs (renameTerm body)
      example2 = joinApps example1 (paramsToArgs (drop (length ls) ps)) in
    example2

optimizeArgs :: Ctxt -> [Arg] -> [Arg]
optimizeArgs g = map (\ (atm, atp) -> (optimizeTerm g atm, atp))

-- Returns whether or not it is safe to substitute a term into another
-- More specifically, returns true when there are no global vars (excluding ctors),
-- no free vars that aren't also free in the other term, and no ambs/fails/uniforms
safe2sub :: Ctxt -> Var -> Term -> Term -> Bool
safe2sub g x xtm tm =
  isLin' x tm || (noDefsSamps xtm && fvsOkay (freeVars' xtm))
  where
    fvsOkay :: FreeVars -> Bool
    -- TODO: don't need to check typeIsRecursive g tp, once we can copy terms with recursive datatypes
    fvsOkay fvs = all (\ (_, tp) -> not (typeHasArr g tp || typeIsRecursive g tp)) (Map.toList fvs)
    
    -- Returns if there are no global def vars or ambs/fails/uniforms
    noDefsSamps :: Term -> Bool
    noDefsSamps (TmVarL x tp) = True
    noDefsSamps (TmVarG DefVar x as tp) = False
    noDefsSamps (TmVarG CtorVar x as tp) = all (noDefsSamps . fst) as
    noDefsSamps (TmLam x tp tm tp') = noDefsSamps tm
    noDefsSamps (TmApp tm1 tm2 tp2 tp) = noDefsSamps tm1 && noDefsSamps tm2
    noDefsSamps (TmLet x xtm xtp tm tp) = noDefsSamps xtm && noDefsSamps tm
    noDefsSamps (TmCase tm tp cs tp') = noDefsSamps tm && all (\ (Case x xps xtm) -> noDefsSamps xtm) cs
    noDefsSamps (TmSamp d tp) = False

optimizeTerm :: Ctxt -> Term -> Term
optimizeTerm g (TmVarL x tp) = TmVarL x tp
optimizeTerm g (TmVarG gv x as tp) =
  TmVarG gv x (optimizeArgs g as) tp
optimizeTerm g (TmLet x xtm xtp tm tp) =
  let xtm' = optimizeTerm g xtm
      tm' = optimizeTerm (ctxtDeclTerm g x xtp) tm in
  if safe2sub g x xtm' tm'
    then optimizeTerm g (substs g [(x, Left xtm')] (renameTerm tm'))
    else TmLet x xtm' xtp tm' tp
optimizeTerm g (TmSamp d tp) = TmSamp d tp
optimizeTerm g (TmLam x tp tm tp') =
  TmLam x tp (optimizeTerm (ctxtDeclTerm g x tp) tm) tp'
optimizeTerm g (TmApp tm1 tm2 tp2 tp) =
  let (body, as) = splitApps (TmApp tm1 tm2 tp2 tp)
      body1 = optimizeTerm g body
      as' = optimizeArgs g as
      (ds, body2) = splitLets body1
      (ls, body3) = splitLams body2
      lets = map (\ ((lx, ltp), (atm, atp)) -> (lx, atm, atp)) (zip ls as')
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
      (ds, TmVarG CtorVar x as _) ->
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
            cs' = map (\ (Case x xps xtm) ->
                         let g' = ctxtDeclArgs g (ps' ++ xps) in
                           Case x xps (peelLams g' ps' (optimizeTerm g' xtm))) cs
        in
          joinLams ps' (TmCase tm' y cs' end)
optimizeTerm g (TmDiscard dtm tm tp) = error "TODO"
optimizeTerm g (TmAmb tms tp) = TmAmb (map (optimizeTerm g) tms) tp

optimizeFile :: Progs -> Either String Progs
optimizeFile ps =
  let g = ctxtDefProgs ps in
    mapProgsM (return . optimizeTerm g) ps
