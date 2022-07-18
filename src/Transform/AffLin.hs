module Transform.AffLin where
import qualified Data.Map as Map
import Control.Monad.RWS
import Struct.Lib
import Util.Helpers
import Scope.Ctxt
import Scope.Name
import Scope.Free
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
--   1. L(tm a1 a2 ... an) = let <f, _> = L(tm) in f L(a1) L(a2) ... L(an)
--   2. L(<tm1, tm2, ..., tmn>) => <L*(tm1), L*(tm2), ..., L*(tmn), L*(unit)>
--        (where L* denotes L but with calls to Z to ensure all branches have same FVs)

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
         (listen (local (\ g -> ctxtDeclTerm g x tp) m) >>= \ (tm, fvs) ->
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
discard' x (TpProd am tps) rtm
  | am == Additive =
    return (TmElimProd Additive x
             [(if i == length tps - 1 then "_x" else "_", tp)| (i, tp) <- enumerate tps]
             rtm (typeof rtm))
  | otherwise = let ps = [(etaName "_" i, tp) | (i, tp) <- enumerate tps] in
      discards (Map.fromList ps) rtm >>= \ rtm' ->
      return (TmElimProd Multiplicative x ps rtm' (typeof rtm'))
discard' x (TpVar y _) rtm =
  ask >>= \ g ->
  maybe2 (ctxtLookupType g y)
    (error ("In Free.hs/discard, unknown type var " ++ y))
    (mapM (\ (Ctor x' as) ->
               let as' = nameParams x' as in
                 alBinds as' (return tmUnit) >>= \ tm ->
                 return (Case x' as' tm))) >>= \ cs' ->
  return (TmLet "_" (TmCase x (y, []) cs' tpUnit) tpUnit rtm (typeof rtm))
discard' x NoTp rtm = error "Trying to discard a NoTp"

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
affLinTp :: Type -> AffLinM Type
affLinTp (TpVar y _) = return (TpVar y [])
affLinTp (TpProd am tps) = pure (TpProd am) <*> mapM affLinTp (tps ++ (if am == Additive then [tpUnit] else []))
affLinTp (TpArr tp1 tp2) =
  let (tps, end) = splitArrows (TpArr tp1 tp2) in
    mapM affLinTp tps >>= \ tps' ->
    affLinTp end >>= \ end' ->
    return (TpProd Additive [joinArrows tps' end', tpUnit])
affLinTp NoTp = error "Trying to affLin a NoTp"

-- Make a case linear, returning the local vars that occur free in it
affLinCase :: Case -> AffLinM Case
affLinCase (Case x ps tm) =
  mapParamsM affLinTp ps >>= \ ps' ->
  alBinds ps' (affLin tm) >>=
  return . Case x ps'

-- Converts a lambda term to an ampersand pair with Unit, where the
-- Unit side discards all the free variables from the body of the lambda
-- ambFun `\ x : T. tm` = `<\ x : T. tm, Z(FV(\ x : T. tm))>`,
ambFun :: Term -> FreeVars -> AffLinM Term
ambFun tm fvs =
  let tp = typeof tm in
    case tp of
      TpArr _ _ ->
        discards fvs tmUnit >>= \ ntm ->
        return (TmProd Additive [(tm, tp), (ntm, tpUnit)])
      _ -> return tm

-- Extract the function from a linearized term, if possible
-- So ambElim `<f, unit>` = `f`
ambElim :: Term -> Term
ambElim tm =
  case typeof tm of
    TpProd Additive [tp, unittp] ->
      TmElimProd Additive tm [("x", tp), ("_", unittp)] (TmVarL "x" tp) tp
    _ -> tm

-- Linearizes params and also a body term
affLinParams :: [Param] -> Term -> AffLinM ([Param], Term)
affLinParams ps body =
  mapParamsM affLinTp ps >>= \ lps ->
  listen (alBinds lps (affLin body)) >>= \ (body', fvs) ->
    return (lps, body')

-- Peels of lambdas as params, returning (L(params), L(body))
affLinLams :: Term -> AffLinM ([Param], Term)
affLinLams = uncurry affLinParams . splitLams

-- Generic helper for applying L to a list of something, where alf=L and dscrd=discard
affLinBranches :: (a -> AffLinM b) -> (FreeVars -> b -> AffLinM b) -> [a] -> AffLinM [b]
affLinBranches alf dscrd als =
  listen (mapM (listen . alf) als) >>= \ (alxs, xsAny) ->
  mapM (\ (b, xs) -> dscrd (Map.difference xsAny xs) b) alxs

-- Make a term linear, returning the local vars that occur free in it
affLin :: Term -> AffLinM Term
affLin (TmVarL x tp) =
  -- L(x) => x    (x is a local var)
  affLinTp tp >>= \ ltp ->
  tell (Map.singleton x ltp) >>
  return (TmVarL x ltp)
affLin (TmVarG gv x tis as y) =
  -- L(x) => x    (x is a global var with type args tis and term args as)
  mapArgsM affLin as >>= \ as' ->
  affLinTp y >>= \ y' ->
  mapM affLinTp tis >>= \ tis' ->
  return (TmVarG gv x tis' as' y')
affLin (TmLam x tp tm tp') =
  -- L(\ x : tp. tm) => <\ x : L(tp). L(tm), Z(FV(tm) - {x})>
  listen (affLinLams (TmLam x tp tm tp')) >>= \ ((lps, body), fvs) ->
  ambFun (joinLams lps body) fvs
affLin (TmApp tm1 tm2 tp2 tp) =
  -- L(tm a1 a2 ... an) => let <f, _> = L(tm) in f L(a1) L(a2) ... L(an)
  let (tm, as) = splitApps (TmApp tm1 tm2 tp2 tp) in
    listen (pure (,) <*> affLin tm <*> mapArgsM affLin as) >>= \ ((tm', as'), fvs) ->
    ambFun (joinApps (ambElim tm') as') fvs
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
  affLinTp tp >>= return . TmCase tm' y cs'
affLin (TmAmb tms tp) =
  -- L(amb tm1 tm2 ... tmn : tp) => amb L*(tm1) L*(tm2) ... L*(tmn) : L(tp)
  -- where L*(tm) = let _ = Z((FV(tm1) ∪ FV(tm2) ∪ ... ∪ FV(tmn)) - FV(tm)) in L(tm)
  affLinBranches affLin discards tms >>= \ tms' ->
  -- Same as in TmCase above, I think the below should work; if not, use type of first tm
  affLinTp tp >>= \ tp' ->
  --  (if null tms' then affLinTp tp else return (typeof (head tms'))) >>= \ tp' ->
  return (TmAmb tms' tp')
affLin (TmFactor wt tm tp) =
  -- L(factor wt in tm: tp) => factor wt in L(tm): L(tp)
  affLin tm >>= \ tm' ->
  affLinTp tp >>= \ tp' ->
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

-- Make an affine Prog linear
affLinProg :: Prog -> AffLinM Prog
affLinProg (ProgData y cs) =
  pure (ProgData y) <*> mapCtorsM affLinTp cs
affLinProg (ProgFun x as tm tp) =
  mapParamsM affLinTp as >>= \ as' ->
  pure (ProgFun x as') <*> alBinds as' (affLin tm) <*> affLinTp tp
affLinProg (ProgExtern x ps tp) =
  pure (ProgExtern x) <*> mapM affLinTp ps <*> affLinTp tp

-- Helper that does affLinTp on all the types so that we can add all the definitions to ctxt
affLinDefine :: Prog -> AffLinM Prog
affLinDefine (ProgData y cs) =
  pure (ProgData y) <*> mapCtorsM affLinTp cs
affLinDefine (ProgFun x as tm tp) =
  pure (ProgFun x) <*> mapParamsM affLinTp as <*> pure tm <*> affLinTp tp
affLinDefine (ProgExtern x ps tp) =
  pure (ProgExtern x) <*> mapM affLinTp ps <*> affLinTp tp

-- Adds all the definitions in a file to context, after replacing arrows with <type, Unit>
affLinDefines :: Progs -> AffLinM Ctxt
affLinDefines (Progs ps end) =
  mapM affLinDefine ps >>= \ ps' ->
  return (ctxtDefProgs (Progs ps' end))

-- Applies L to all the defs in a file
affLinProgs :: Progs -> AffLinM Progs
affLinProgs (Progs ps end) =
  affLinDefines (Progs ps end) >>= \ g ->
  local (const g) (pure Progs <*> mapM affLinProg ps <*> affLin end)

-- Runs the AffLin monad
runAffLin :: Progs -> Progs
runAffLin ps = case runRWS (affLinProgs ps) emptyCtxt () of
  (Progs ps' end, mtps, _) -> Progs ps' end

-- Make an affine file linear
affLinFile :: Progs -> Either String Progs
affLinFile = return . runAffLin
