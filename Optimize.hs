module Optimize where
import Data.List
import Exprs
import Ctxt
import Util
import Name
import Rename

{- Provides various optimizations:
1. (case t of C1 a* -> \x. t1 | C2 b* -> \y. t2 | C3 c* -> t3)
     -> (\x. case t of C1 a* -> t1 | C2 b* -> t2[y := x] | C3 c* -> t3 x)
2. (\ x. f) t   ->   (let x = t in f)
3. (case C4 t* of C1 a* -> t1 | ... | C4 d* -> t4 | ...) -> (let d* = t* in t4)
4. (let x = t1 in t2) -> (t2[x := t1])     where x occurs *exactly* once in t2
5. (define y = \ a*. x a*; ...) -> ...[y := x]

Notes:
- Optimization (1) enforces the invariant that the return type of every case-of is not
  an arrow type.

- Optimization (4) only happens when the let-bound variable occurs exactly once in its
  body. Consider if we did this unconditionally:
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

-- Peels off the lams around a term and substitutes their bound variables for others
-- Example 1: peelLams g [(x, Bool)] (\ z : Bool. and true z) = (and true x)
-- Example 2: peelLams g [(x, Bool)] (and true) = (and true x)
peelLams :: Ctxt -> [Param] -> Term -> Term
peelLams g ps tm =
  let (ls, body) = splitLams tm in
    joinApps
      (substs g (zip (map fst ls) (map fst ps)) (renameTerm body)) -- Example 1
      (paramsToArgs (drop (length ls) ps))                         -- Example 2

liftCase :: Ctxt -> Term -> Term
liftCase g (TmLam x tp tm tp') =
  TmLam x tp (liftCase g tm) tp'
liftCase g (TmApp tm1 tm2 tp2 tp) =
  let (body, as) = splitApps (TmApp tm1 tm2 tp2 tp)
      body' = liftCase g body
      (ls, body'') = splitLams body'
      lets = zip ls as
      rem_as = drop (length lets) as
      rem_ls = drop (length lets) ls
      let_tm = foldr (\ ((lx, ltp), (atm, atp)) bdy -> TmLet lx atm atp bdy (getType bdy)) body'' lets
  in
    -- Either rem_as or rem_ls must be [], so just expand with both:
    joinLams rem_ls (joinApps let_tm rem_as)
liftCase g (TmCase tm y cs (TpArr tp1 tp2)) =
  let (ps, end) = splitArrows (TpArr tp1 tp2)
      g_ps = foldr (\ (Case x xps xtm) g-> ctxtDeclArgs g xps) g cs
      ps' = reverse $ snd $ foldl (\ (e, ps') p -> let e' = freshVar (ctxtDeclTerm g_ps e (TpVar "")) e in (e', (e', p) : ps')) (etaName "e" 0, []) ps
      cs' = map (\ (Case x xps xtm) -> Case x xps
                  (peelLams (ctxtDeclArgs g (ps' ++ xps)) ps' xtm)) cs
  in
    joinLams ps' (TmCase tm y cs' end)
liftCase g tm = tm
