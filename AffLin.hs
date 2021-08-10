module AffLin where
import qualified Data.Map as Map
import Data.List
import Exprs
import Ctxt
import Util
import Name
import Rename
import Free

{- ====== Affine to Linear Functions ====== -}
-- These functions convert affine terms to
-- linear ones, where an affine term is one where
-- every bound var occurs at most once, and a
-- linear term is one where every bound var
-- occurs exactly once


-- Uses x without changing the value or type of a term
-- For example, take x : Bool and some term tm that becomes
-- case (case x of false -> unit | true -> unit) of unit -> tm
discard' :: Ctxt -> Var -> Type -> Term -> Term
discard' g x (TpArr tp1 tp2) tm =
  error ("Can't discard " ++ x ++ " : " ++ show (TpArr tp1 tp2))
discard' g x (TpVar y) tm = maybe2 (ctxtLookupType g y)
  (error ("In Free.hs/discard, unknown type var " ++ y))
  $ \ cs ->
      TmCase (TmVarL x (TpVar y)) (TpVar y)
        (map (\ (Ctor x' as) ->
                let as' = nameParams x' (map aff2linTp as) in
                  Case x' as' (foldr (uncurry $ discard g) tm as'))
          cs) (getType tm)
discard' g x (TpMaybe tp) tm =
  let x' = aff2linName x
      tp' = getType tm in
    tmElimMaybe (TmVarL x (TpMaybe tp)) tp tm (x', TmSamp DistFail tp') tp'

discard :: Ctxt -> Var -> Type -> Term -> Term
discard g x tp tm
  | typeHasArr g tp = tmElimUnit (discard' g x tp tmUnit) tm (getType tm)
  | otherwise = tm

-- Discard a set of variables
discards :: Ctxt -> FreeVars -> Term -> Term
discards g fvs tm = Map.foldrWithKey (discard g) tm fvs

-- Convert the type of an affine term to what it will be when linear
-- That is, recursively change every T1 -> T2 to be Maybe (T1 -> T2)
aff2linTp :: Type -> Type
aff2linTp (TpVar y) = TpVar y
aff2linTp (TpArr tp1 tp2) = TpMaybe (TpArr (aff2linTp tp1) (aff2linTp tp2))
aff2linTp tp = error ("aff2linTp shouldn't see a " ++ show tp)

-- Make a case linear, returning the local vars that occur free in it
aff2linCase :: Ctxt -> Case -> (Case, FreeVars)
aff2linCase g (Case x ps tm) =
  let ps' = map (\ (a, atp) -> (a, aff2linTp atp)) ps
      (tm', fvs) = aff2linh (ctxtDeclArgs g ps') tm
      -- Need to discard all ps' that do not occur free in tm'
      tm'' = discards g (Map.difference (Map.fromList ps') fvs) tm' in
    (Case x ps' tm'', foldr (Map.delete . fst) fvs ps')

aff2linUnfoldMaybe :: Term -> Term -> Term
aff2linUnfoldMaybe tm1 tm2 = case getType tm1 of
  TpMaybe (TpArr tp2 tp) ->
    let jx = etaName tmJustName 0
        arr = TpArr tp2 tp in
      tmElimMaybe tm1 arr (TmSamp DistFail tp) (jx, TmApp (TmVarL jx arr) tm2 tp2 tp) tp
  (TpArr tp2 tp) ->
    TmApp tm1 tm2 tp2 tp
  _ -> error "internal error: aff2linUnfoldMaybe app on non-arrow type"

aff2linJoinApps :: Term -> [Arg] -> Term
aff2linJoinApps = foldl (\ tm (atm, atp) -> aff2linUnfoldMaybe tm atm)

-- Make a term linear, returning the local vars that occur free in it
aff2linh :: Ctxt -> Term -> (Term, FreeVars)
aff2linh g (TmVarL x tp) =
  let ltp = aff2linTp tp in
    (TmVarL x ltp, Map.singleton x ltp)
aff2linh g (TmVarG gv x as y) =
  let (as', fvss) = unzip $ flip map as $
        \ (tm, tp) -> let (tm', xs) = aff2linh g tm in ((tm', aff2linTp tp), xs) in
  (TmVarG gv x as' y, Map.unions fvss)
aff2linh g (TmLam x tp tm tp') =
  let ltp = aff2linTp tp
      ltp' = aff2linTp tp'
      tparr = TpArr ltp ltp'
      (tm', fvs) = aff2linh (ctxtDeclTerm g x ltp) tm
      fvs' = Map.delete x fvs
      tm'' = if Map.member x fvs then tm' else discard g x ltp tm'
      jtm = tmMaybe (Just (TmLam x ltp tm'' ltp')) tparr
      ntm = discards g fvs' (tmMaybe Nothing tparr) in
    (TmAmb [ntm, jtm] (TpMaybe tparr), fvs')
aff2linh g (TmApp tm1 tm2 tp2 tp) = -- TODO: pass number of args (increment here), so we don't necessarily need to do this amb stuff? And what about if tm2 has arrow type but is always used in tm1?
  let (tm1', fvs1) = aff2linh g tm1
      (tm2', fvs2) = aff2linh g tm2
  in
    (aff2linUnfoldMaybe tm1' tm2', Map.union fvs1 fvs2)
aff2linh g (TmLet x xtm xtp tm tp) =
  let xtp' = aff2linTp xtp
      tp' = aff2linTp tp
      (xtm', fvsx) = aff2linh g xtm
      (tm', fvs) = aff2linh (ctxtDeclTerm g x xtp') tm
      tm'' = if Map.member x fvs then tm' else discard g x xtp' tm'
  in
    (TmLet x xtm' xtp' tm'' tp', Map.union fvsx (Map.delete x fvs))
aff2linh g (TmCase tm y cs tp) =
  let csxs = map (aff2linCase g) cs
      xsAny = Map.unions (map snd csxs)
      (tm', tmxs) = aff2linh g tm
      cs' = flip map csxs $ \ (Case x as tm', xs) -> Case x as $
                  -- Need to discard any vars that occur free in other cases, but that
                  -- don't in this one bc all cases must have same set of free vars
                  discards (ctxtDeclArgs g as) (Map.difference xsAny xs) tm' in
    (TmCase tm' y cs' (aff2linTp tp), Map.union xsAny tmxs)
aff2linh g (TmSamp d tp) = (TmSamp d (aff2linTp tp), Map.empty)
aff2linh g (TmAmb tms tp) =
  let tfvs = map (aff2linh g) tms
      all_fvs = Map.unions (map snd tfvs)
      tms' = map (\ (tm', fvs) -> discards g (Map.difference all_fvs fvs) tm') tfvs
  in
    (TmAmb tms' (aff2linTp tp), all_fvs)

-- Make an affine Prog linear
aff2linProg :: Ctxt -> Prog -> Prog
aff2linProg g (ProgFun x (p : ps) tm tp) =
  error "Function shouldn't have params before affine-to-linear transformation"
aff2linProg g (ProgExtern x xp (p : ps) tp) =
  error "Extern shouldn't have params before affine-to-linear transformation"
aff2linProg g (ProgFun x [] tm tp) =
  let (as, endtp) = splitArrows tp
      (ls, endtm) = splitLams tm
      as' = map aff2linTp as
      ls' = map (fmap aff2linTp) ls
      etas = map (\ (i, atp) -> (etaName x i, atp)) (drop (length ls') (enumerate as'))
      g' = ctxtDeclArgs g ls'
      (endtm', fvs) = aff2linh g' endtm
      endtm'' = discards g' (Map.difference (Map.fromList ls') fvs) endtm'
      endtp' = aff2linTp endtp -- This may not be necessary, but is future-proof
  in
    ProgFun x (ls' ++ etas) (aff2linJoinApps endtm'' (paramsToArgs etas)) endtp'
aff2linProg g (ProgExtern x xp [] tp) =
  let (as, end) = splitArrows tp
      as' = map aff2linTp as in
    ProgExtern x xp as' end
aff2linProg g (ProgData y cs) =
  ProgData y (map (\ (Ctor x as) -> Ctor x (map aff2linTp as)) cs)

unitProg :: Prog
unitProg = ProgData tpUnitName unitCtors

-- Make an affine file linear
aff2linFile :: Progs -> Either String Progs
aff2linFile (Progs ps end) =
  let ps' = ps ++ [unitProg]
      g = ctxtDefProgs (Progs ps' end)
      (ls, endtm) = splitLams end in
    return (Progs (map (aff2linProg g) ps') (joinLams ls (fst (aff2linh g endtm))))
