module Transform.AffLin where
import qualified Data.Map as Map
import Control.Monad.RWS
import Struct.Lib
import Util.Helpers
import Scope.Ctxt (Ctxt, ctxtDefLocal, ctxtDefProgs, emptyCtxt)
import Scope.Name
import Scope.Free (robust)
import Scope.Subst

{- ====== Affine to Linear Functions ====== -}
-- These functions convert affine terms to
-- linear ones, where an affine term is one where
-- every bound var occurs at most once, and a
-- linear term is one where every bound var
-- occurs exactly once.
-- 
-- In comments, Z = discards, L = affLin, FV = freeVars
-- 
-- We apply the following transformations to types,
-- rewriting terms so that they have the new transformed type:
--   1. L(tp1 -> tp2 -> ... -> tpn) = (L(tp1) -> L(tp2) -> ... -> L(tpn)) & Unit
--   2. L(tp1 &  tp2 *  ... &  tpn) =  L(tp1) &  L(tp2) &  ... &  L(tpn)  & Unit
-- Then for terms, we basically apply these two transformations to match the new types:
--   1. L(\x1. ... tm) = <\x1. ... L(tm), L*(unit)>
--      L(tm a1 a2 ... an) = L(tm).1 L(a1) L(a2) ... L(an)
--   2. L(<tm1, tm2, ..., tmn>) = <L*(tm1), L*(tm2), ..., L*(tmn), L*(unit)>
--        (where L* denotes L but with calls to Z to ensure all branches have same FVs)
--      L(tm.i) = L(tm).i


-- Reader, Writer, State monad
type AffLinM a = RWS Ctxt FreeVars () a
-- RWS monad functions, where
--   m = RWS monad
--   r = reader type
--   w = writer type
--   s = state type
--
-- === r ===
-- ask :: m r                         (returns current r)
-- local :: (r -> r) -> m a -> m a    (temporarily modifies r)
--
-- === w ===
-- tell :: w -> m ()                  (sets w)
-- censor :: (w -> w) -> m a -> m a   (modifies the w that was returned)
-- listen :: m a -> m (a, w)          (also returns w)
--
-- === s ===
-- get :: m s                         (returns current s)
-- put :: s -> m ()                   (sets s)
-- modify :: (s -> s) -> m ()         (modifies s)




-- Bind x : tp inside an AffLinM, discarding it if unused
alBind :: Var -> Type -> AffLinM Term -> AffLinM Term
alBind x tp m =
  censor (Map.delete x) -- Delete x from FVs
         (listen (local (\ g -> ctxtDefLocal g x tp) m) >>= \ (tm, fvs) ->
            -- Discard if necessary
            if Map.member x fvs then return tm else discard x tp tm)

-- Bind a list of params inside an AffLinM
-- Like alBind, but for multiple params
alBinds :: [Param] -> AffLinM Term -> AffLinM Term
alBinds ps m = foldl (\ m (x, tp) -> alBind x tp m) m ps

-- Maps something to Unit
-- For example, take x : Bool, which becomes
-- case x of false -> unit | true -> unit
discard' :: Term -> Type -> Term -> AffLinM Term
discard' (TmVarL "_" tp') tp rtm = return rtm -- error ("discard' \"_\" " ++ show tp ++ " in the term " ++ show rtm)
discard' x (TpArr tp1 tp2) rtm =
  error ("Can't discard " ++ show x ++ " : " ++ show (TpArr tp1 tp2))
discard' x (TpProd Additive tps) rtm =
    return (TmElimProd Additive x
             [(if i == length tps - 1 then "_x" else "_", tp)| (i, tp) <- enumerate tps]
             rtm (typeof rtm))
discard' x (TpProd Multiplicative tps) rtm =
    let ps = [(etaName "_" i, tp) | (i, tp) <- enumerate tps] in
      discards (Map.fromList ps) rtm >>= \ rtm' ->
      return (TmElimProd Multiplicative x ps rtm' (typeof rtm'))
discard' x xtp@(TpData y []) rtm =
  ask >>= \ g ->
    -- let () = discard x in rtm
    return (TmElimProd Multiplicative (TmVarG DefVar (discardName y) [] [] [(x, xtp)] tpUnit) [] rtm (typeof rtm))
discard' _ tp _ = error ("Trying to discard a " ++ show tp)

-- If x : tp contains an affinely-used function, we sometimes need to discard
-- it to maintain correct probabilities, but without changing the value or type
-- of some term. This maps x to Unit, then case-splits on it.
-- So to discard x : (A -> B) & Unit in tm, this returns
-- case x.2 of unit -> tm
discard :: Var -> Type -> Term -> AffLinM Term
discard x tp tm =
  ask >>= \ g ->
  if robust g tp
    then return tm
    else (discard' (TmVarL x tp) tp tm){- >>= \ dtm ->
          return (TmLet "_" dtm tpUnit tm (typeof tm)))-}

-- Discard a set of variables
discards :: FreeVars -> Term -> AffLinM Term
discards fvs tm = Map.foldlWithKey (\ tm x tp -> tm >>= discard x tp) (return tm) fvs

-- See definition of L(tp) above
affLinTp :: Type -> Type
affLinTp (TpData y []) = TpData y []
affLinTp (TpProd am tps) = TpProd am $ map affLinTp tps ++ [tpUnit | am == Additive]
affLinTp (TpArr tp1 tp2) =
  TpProd Additive [TpArr (affLinTp tp1) (affLinTp tp2), tpUnit]
affLinTp tp = error ("Trying to affLin a " ++ show tp)

-- Make a case linear, returning the local vars that occur free in it
affLinCase :: Case -> AffLinM Case
affLinCase (Case x ps tm) =
  let ps' = mapParams affLinTp ps in
  alBinds ps' (affLin tm) >>=
  return . Case x ps'

-- Linearizes params and also a body term
affLinParams :: [Param] -> Term -> AffLinM ([Param], Term)
affLinParams ps body =
  let lps = mapParams affLinTp ps in
  alBinds lps (affLin body) >>= \ body' ->
    return (lps, body')

-- Generic helper for applying L to a list of something, where alf=L and dscrd=discard
affLinBranches :: (a -> AffLinM b) -> (FreeVars -> b -> AffLinM b) -> [a] -> AffLinM [b]
affLinBranches alf dscrd als =
  listen (mapM (listen . alf) als) >>= \ (alxs, xsAny) ->
  mapM (\ (b, xs) -> dscrd (Map.difference xsAny xs) b) alxs

-- Make a term linear, returning the local vars that occur free in it
affLin :: Term -> AffLinM Term
affLin (TmVarL x tp) =
  -- L(x) => x    (x is a local var)
  let ltp = affLinTp tp in
  tell (Map.singleton x ltp) >>
  return (TmVarL x ltp)
affLin (TmVarG gv x [] tis as y) =
  -- x is a global var with args as
  -- or a constructor with type args tis and args as
  -- L(x a1 ...) => x L(a1) ...
  mapArgsM affLin as >>= \ as' ->
  let y'   = affLinTp y
      tis' = map affLinTp tis
  in return (TmVarG gv x tis' as' y')
affLin (TmLam x xtp tm tp) =
  -- L(\ x : xtp. tm) => <\ x : L(xtp). L(tm), Z(FV(tm) - {x})>
  let xtp' = affLinTp xtp
      tp'  = affLinTp tp in
  listen (alBind x xtp' (affLin tm)) >>= \ (tm', fvs) ->
  discards fvs tmUnit >>= \ ntm ->
  return (TmProd Additive [(TmLam x xtp' tm' tp', TpArr xtp' tp'), (ntm, tpUnit)])
affLin (TmApp tm1 tm2 tp2 tp) =
  -- L(tm1 tm2 : tp) => let <f, _> = L(tm1 : tp1) in f L(tm2 : tp2)
  affLin tm1 >>= \ tm1' -> affLin tm2 >>= \ tm2' ->
  let tp2' = affLinTp tp2
      tp'  = affLinTp tp
      tp1' = TpArr tp2' tp' in
  return (TmApp (TmElimProd Additive tm1' [("x", tp1'), ("_", tpUnit)]
                            (TmVarL "x" tp1') tp1')
                tm2' tp2' tp')
affLin (TmLet x xtm xtp tm tp) =
  -- L(let x : xtp = xtm in tm) => let x : L(xtp) = L(xtm) in let _ = Z({x} - FV(tm)) in L(tm)
  affLin xtm >>= \ xtm' ->
  let xtp' = typeof xtm' in
    alBind x xtp' (affLin tm) >>= \ tm' ->
    return (TmLet x xtm' xtp' tm' (typeof tm'))
affLin (TmCase tm y cs tp) =
  -- L(case tm of C1 | C2 | ... | Cn) => case L(tm) of L*(C1) | L*(C2) | ... | L*(Cn),
  -- where L*(C) = let _ = Z((FV(C1) ∪ FV(C2) ∪ ... ∪ FV(Cn)) - FV(C)) in L(C)
  affLin tm >>= \ tm' ->
  affLinBranches affLinCase
    (\ xs (Case x as tm) -> fmap (Case x as) (discards xs tm)) cs >>= \ cs' ->
  return (TmCase tm' y cs' (affLinTp tp))
affLin (TmAmb tms tp) =
  -- L(amb tm1 tm2 ... tmn : tp) => amb L*(tm1) L*(tm2) ... L*(tmn) : L(tp)
  -- where L*(tm) = let _ = Z((FV(tm1) ∪ FV(tm2) ∪ ... ∪ FV(tmn)) - FV(tm)) in L(tm)
  affLinBranches affLin discards tms >>= \ tms' ->
  -- Same as in TmCase above, I think the below should work; if not, use type of first tm
  let tp' = affLinTp tp in
  --  let tp' = if null tms' then affLinTp tp else typeof (head tms') in
  return (TmAmb tms' tp')
affLin (TmFactor wt tm tp) =
  -- L(factor wt in tm: tp) => factor wt in L(tm): L(tp)
  affLin tm >>= \ tm' ->
  let tp' = affLinTp tp in
  return (TmFactor wt tm' tp')
affLin (TmProd am as)
  | am == Additive =
    -- L(<tm1, tm2, ..., tmn>) => <L*(tm1), L*(tm2), ..., L*(tmn), L*(unit)>,
    -- where L*(tm) = let _ = Z((FV(tm1) ∪ FV(tm2) ∪ ... ∪ FV(tmn)) - FV(tm)) in L(tm)
    pure (TmProd am) <*> affLinBranches (mapArgM affLin) (mapArgM . discards) (as ++ [(tmUnit, tpUnit)])
  | otherwise =
    -- L(tm1, tm2, ..., tmn) => (L(tm1), L(tm2), ..., L(tmn))
    pure (TmProd am) <*> mapArgsM affLin as
affLin (TmElimProd Additive tm ps tm' tp) =
  -- L(let <x1, x2, ..., xn> = tm in tm') =>
  --    let <x1, x2, ..., xn> = L(tm) in let _ = Z({x1, x2, ..., xn} - FV(tm')) in L(tm')
  affLin tm >>= \ tm ->
  affLinParams ps tm' >>= \ (ps, tm') ->
  return (TmElimProd Additive tm (ps ++ [("_", tpUnit)]) tm' (typeof tm'))
affLin (TmElimProd Multiplicative tm ps tm' tp) =
  -- L(let (x1, x2, ..., xn) = tm in tm') =>
  --    let (x1, x2, ..., xn) = L(tm) in let _ = Z({x1, x2, ..., xn} - FV(tm')) in L(tm')
  affLin tm >>= \ tm ->
  affLinParams ps tm' >>= \ (ps, tm') ->
  return (TmElimProd Multiplicative tm ps tm' (typeof tm'))
affLin (TmEqs tms) =
  -- L(tm1 == tm2 == ... == tmn) =>
  --   L(tm1) == L(tm2) == ... == L(tmn)
  pure TmEqs <*> mapM affLin tms

-- Generate a discard function for each recursive type
affLinDiscards :: [Prog] -> AffLinM [Prog]
affLinDiscards (p@(ProgData y cs) : ps) =
  ask >>= \ g ->
  let ytp = TpData y [] in
  if robust g ytp then
    pure (p :) <*> affLinDiscards ps
  else
    let
      -- define _discardy_ = \x. case x of Con1 a11 a12 ... -> () | ...
      -- Linearizing this will generate recursive calls to discard as needed
      defDiscard = ProgFun (discardName y) [("x", ytp)] body tpUnit
      body = TmCase (TmVarL "x" ytp) (y, []) cases tpUnit
      cases = [let atps' = nameParams c atps in Case c atps' tmUnit | Ctor c atps <- cs]
    in
      affLinDiscards ps >>= \ ps' ->
      return (defDiscard : p : ps')
affLinDiscards (p : ps) = pure (p :) <*> affLinDiscards ps
affLinDiscards [] = return []

-- Make an affine Prog linear
affLinProg :: Prog -> AffLinM Prog
affLinProg (ProgData y cs) =
  pure (ProgData y (mapCtors affLinTp cs))
affLinProg (ProgFun x as tm tp) =
  let as' = mapParams affLinTp as
      tp' = affLinTp tp
  in pure (\tm' -> ProgFun x as' tm' tp') <*> alBinds as' (affLin tm)
affLinProg (ProgExtern x ps tp) =
  pure (ProgExtern x (map affLinTp ps) (affLinTp tp))

-- Helper that does affLinTp on all the types so that we can add all the definitions to ctxt
affLinDefine :: Prog -> Prog
affLinDefine (ProgData y cs) =
  ProgData y (mapCtors affLinTp cs)
affLinDefine (ProgFun x as tm tp) =
  ProgFun x (mapParams affLinTp as) tm (affLinTp tp)
affLinDefine (ProgExtern x ps tp) =
  ProgExtern x (map affLinTp ps) (affLinTp tp)

-- Adds all the definitions in a file to context, after replacing arrows with <type, Unit>
affLinDefines :: Progs -> Ctxt
affLinDefines (Progs ps end) =
  let ps' = map affLinDefine ps in
  ctxtDefProgs (Progs ps' end)

-- Applies L to all the defs in a file
affLinProgs :: Progs -> AffLinM Progs
affLinProgs (Progs ps end) =
  let g = affLinDefines (Progs ps end) in
  local (const g) (affLinDiscards ps >>= \ ps' -> pure Progs <*> mapM affLinProg ps' <*> affLin end)

-- Runs the AffLin monad
runAffLin :: Progs -> Progs
runAffLin ps = case runRWS (affLinProgs ps) emptyCtxt () of
  (Progs ps' end, (), fvs) ->
    if Map.null fvs then Progs ps' end
    else error "affLinProgs leaked bindings"

-- Make an affine file linear
affLinFile :: Progs -> Either String Progs
affLinFile = return . runAffLin
