module AffLin where
import qualified Data.Map as Map
import Control.Monad.RWS
import Exprs
import Ctxt
import Util
import Name
import Free

{- ====== Affine to Linear Functions ====== -}
-- These functions convert affine terms to
-- linear ones, where an affine term is one where
-- every bound var occurs at most once, and a
-- linear term is one where every bound var
-- occurs exactly once

-- In comments, Z = discards, L = affLin, FV = freeVars

-- Reader, Writer, State monad
type AffLinM a = RWS Ctxt FreeVars () a
-- Let m = monad type, r = reader type, w = writer type, and s = state type. Then
--
-- ask :: m r
-- local :: (r -> r) -> m a -> m a
--
-- tell :: w -> m ()
-- censor :: (w -> w) -> m a -> m a
-- listen :: m a -> m (a, w)
--
-- get :: m s
-- put :: s -> m ()
-- modify :: (s -> s) -> m ()

-- Bind x : tp inside an AffLinM
alBind :: Var -> Type -> AffLinM Term -> AffLinM Term
alBind x tp m =
  censor (Map.delete x)
         (listen (local (\ g -> ctxtDeclTerm g x tp) m) >>= \ (tm, fvs) ->
            if Map.member x fvs then return tm else discard x tp tm)

-- Bind a list of params inside an AffLinM
alBinds :: [Param] -> AffLinM Term -> AffLinM Term
alBinds ps m = foldl (\ m (x, tp) -> alBind x tp m) m ps

-- Maps something to Unit
-- For example, take x : Bool, which becomes
-- case x of false -> unit | true -> unit
discard' :: Term -> Type -> AffLinM Term
discard' x (TpArr tp1 tp2) =
  error ("Can't discard " ++ show x ++ " : " ++ show (TpArr tp1 tp2))
discard' x (TpAmp tps) = discard' (TmAmpOut x tps (length tps - 1)) (last tps)
discard' x (TpProd tps) = let ps = [(etaName "_" i, tp) | (i, tp) <- enumerate tps] in discards (Map.fromList ps) tmUnit >>= \ tm -> return (TmProdOut x ps tm tpUnit)
discard' x (TpVar y) =
  ask >>= \ g ->
  maybe2 (ctxtLookupType g y)
    (error ("In Free.hs/discard, unknown type var " ++ y))
    (mapM (\ (Ctor x' as) ->
               let as' = nameParams x' as in
                 alBinds as' (return tmUnit) >>= \ tm ->
                 return (Case x' as' tm))) >>= \ cs' ->
  return (TmCase x y cs' tpUnit)

-- If x : tp contains an affinely-used function, we sometimes need to discard
-- it to maintain correct probabilities, but without changing the value or type
-- of some term. This maps x to Unit, then case-splits on it.
-- So to discard x : (A -> B) & Unit in tm, this returns
-- case x.2 of unit -> tm
discard :: Var -> Type -> Term -> AffLinM Term
discard x tp tm =
  ask >>= \ g ->
  if useOnlyOnce g tp
    then (discard' (TmVarL x tp) tp >>= \ dtm ->
          return (TmLet "_" dtm tpUnit tm (getType tm)))
    else return tm

-- Discard a set of variables
discards :: FreeVars -> Term -> AffLinM Term
discards fvs tm = Map.foldlWithKey (\ tm x tp -> tm >>= discard x tp) (return tm) fvs

-- Convert the type of an affine term to what it will be when linear
-- That is, apply the following transformations:
--   `T1 -> T2 -> ... -> Tn`    =>    `(T1 -> T2 -> ... -> Tn) & Unit`
--   `T1 & T2 & ... & Tn`       =>    `T1 & T2 & ... & Tn & Unit`
-- So that if we want to discard such a term, we can just select its
-- (n+1)th element, which is Unit, and discard that
affLinTp :: Type -> AffLinM Type
affLinTp (TpVar y) = return (TpVar y)
affLinTp (TpAmp tps) = pure TpAmp <*> mapM affLinTp (tps ++ [tpUnit])
affLinTp (TpProd tps) = pure TpProd <*> mapM affLinTp tps
affLinTp (TpArr tp1 tp2) =
  let (tps, end) = splitArrows (TpArr tp1 tp2) in
    mapM affLinTp tps >>= \ tps' ->
    affLinTp end >>= \ end' ->
    return (TpAmp [joinArrows tps' end', tpUnit])

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
  let tp = getType tm in
    case tp of
      TpArr _ _ ->
        discards fvs tmUnit >>= \ ntm ->
        return (TmAmpIn [(tm, tp), (ntm, tpUnit)])
      _ -> return tm

-- Extract the function from a linearized term, if possible
-- So ambElim `<f, unit>` = `f`
ambElim :: Term -> Term
ambElim tm =
  case getType tm of
    TpAmp [tp, unittp] ->
      TmAmpOut tm [tp, unittp] 0
    _ -> tm

affLinParams :: [Param] -> Term -> AffLinM ([Param], Term, FreeVars)
affLinParams ps body =
  mapParamsM affLinTp ps >>= \ lps ->
  listen (alBinds lps (affLin body)) >>= \ (body', fvs) ->
  return (lps, ambElim body', fvs)
      
affLinLams :: Term -> AffLinM ([Param], Term, FreeVars)
affLinLams = uncurry affLinParams . splitLams

affLinBranches :: (a -> AffLinM b) -> (FreeVars -> b -> AffLinM b) -> [a] -> AffLinM [b]
affLinBranches alf dscrd als =
  listen (mapM (listen . alf) als) >>= \ (alxs, xsAny) ->
  mapM (\ (b, xs) -> dscrd (Map.difference xsAny xs) b) alxs

-- Make a term linear, returning the local vars that occur free in it
affLin :: Term -> AffLinM Term
affLin (TmVarL x tp) =
  -- L(`x`) => `x`
  affLinTp tp >>= \ ltp ->
  tell (Map.singleton x ltp) >>
  return (TmVarL x ltp)
affLin (TmVarG gv x as y) =
  -- L(x) => x
  mapArgsM affLin as >>= \ as' ->
  affLinTp y >>= \ y' ->
  return (TmVarG gv x as' y')
affLin (TmLam x tp tm tp') =
  -- L(\ x : tp. tm) => <\ x : tp. L(tm), Z(FV(\ x : tp. tm))>
  affLinLams (TmLam x tp tm tp') >>= \ (lps, body, fvs) ->
  ambFun (joinLams lps body) fvs
affLin (TmApp tm1 tm2 tp2 tp) =
  -- L(tm1 tm2) => L(tm1).1 L(tm2)
  let (tm, as) = splitApps (TmApp tm1 tm2 tp2 tp) in
    listen (pure (,) <*> affLin tm <*> mapArgsM affLin as) >>= \ ((tm', as'), fvs) ->
    ambFun (joinApps (ambElim tm') as') fvs
affLin (TmLet x xtm xtp tm tp) =
  -- L(let x = xtm in tm) => let x = L(xtm) in L(tm)
  affLin xtm >>= \ xtm' ->
  let xtp' = getType xtm' in
    alBind x xtp' (affLin tm) >>= \ tm' ->
    return (TmLet x xtm' xtp' tm' (getType tm'))
affLin (TmCase tm y cs tp) =
  -- L(case tm of C1 | C2 | ... | Cn) => case L(tm) of L*(C1) | L*(C2) | ... | L*(Cn),
  -- where L*(C) = let _ = Z((FV(C1) ∪ FV(C2) ∪ ... ∪ FV(Cn)) - FV(C)) in L(C)
  affLin tm >>= \ tm' ->
  affLinBranches affLinCase
    (\ xs (Case x as tm) -> fmap (Case x as) (discards xs tm)) cs >>= \ cs' ->
  -- I think that the below line should work fine...
  -- If buggy, try to use the type of the first case
  affLinTp tp >>= return . TmCase tm' y cs'
{-  case cs' of
    [] -> affLinTp tp >>= return . TmCase tm' y cs'
    (Case _ _ xtm) : rest -> return (TmCase tm' y cs' (getType xtm))
-}
affLin (TmSamp d tp) =
  -- L(sample d) => sample d
  affLinTp tp >>= \ tp' ->
  return (TmSamp d tp')
affLin (TmAmb tms tp) =
  -- L(amb tm1 tm2 ... tmn) => amb L*(tm1) L*(tm2) ... L*(tmn)
  -- where L*(tm) = let _ = Z((FV(tm1) ∪ FV(tm2) ∪ ... ∪ FV(tmn)) - FV(tm)) in L(tm)
  affLinBranches affLin discards tms >>= \ tms' ->
  -- Same as in TmCase above, I think the below should work; if not, use type of first tm
  affLinTp tp >>= \ tp' ->
  --  (if null tms' then affLinTp tp else return (getType (head tms'))) >>= \ tp' ->
  return (TmAmb tms' tp')
affLin (TmAmpIn as) =
  -- L(<tm1, tm2, ..., tmn>) => <L*(tm1), L*(tm2), ..., L*(tmn), L*(unit)>,
  -- where L*(tm) = let _ = Z((FV(tm1) ∪ FV(tm2) ∪ ... ∪ FV(tmn)) - FV(tm)) in L(tm)
  pure TmAmpIn <*> affLinBranches (mapArgM affLin) (mapArgM . discards) (as ++ [(tmUnit, tpUnit)])
affLin (TmAmpOut tm tps o) =
  -- L(tm.o) => L(tm).on
  pure TmAmpOut <*> affLin tm <*> mapM affLinTp (tps ++ [tpUnit]) <*> pure o
affLin (TmProdIn as) =
  -- L(tm1, tm2, ..., tmn) => (L(tm1), L(tm2), ..., L(tmn))
  pure TmProdIn <*> mapArgsM affLin as
affLin (TmProdOut tm ps tm' tp) =
  -- L(let (x1, x2, ..., xn) = tm in tm') =>
  --    let (x1, x2, ..., xn) = L(tm) in let _ = Z({x1, x2, ..., xn} - FV(tm')) in L(tm')
  affLin tm >>= \ tm ->
  affLinParams ps tm' >>= \ (ps, tm', fvs) ->
  -- Discard all ps that are not used in tm'
  discards (Map.intersection (Map.fromList ps) fvs) tm' >>= \ tm' ->
  return (TmProdOut tm ps tm' (getType tm'))

-- Make an affine Prog linear
affLinProg :: Prog -> AffLinM Prog
affLinProg (ProgFun x _ tm tp) =
  let (as, endtp) = splitArrows tp
      (ls, endtm) = splitLams tm
      etas = [ (etaName x i, atp) | (i, atp) <- drop (length ls) (enumerate as) ]
      endtm_eta = joinApps endtm (paramsToArgs etas)
      ls_eta = ls ++ etas
  in
    mapM affLinTp as >>= \ as' ->
    mapParamsM affLinTp ls_eta >>= \ ls_eta' ->
    alBinds ls_eta' (affLin endtm_eta) >>= \ endtm' ->
    return (ProgFun x ls_eta' endtm' (getType endtm'))
affLinProg (ProgExtern x xp _ tp) =
  let (as, end) = splitArrows tp in
    mapM affLinTp as >>= \ as' ->
    return (ProgExtern x xp as' end)
affLinProg (ProgData y cs) =
  pure (ProgData y) <*> mapCtorsM affLinTp cs

-- Helper
affLinDefine :: Prog -> AffLinM Prog
affLinDefine (ProgData y cs) =
  pure (ProgData y) <*> mapCtorsM affLinTp  cs
affLinDefine (ProgFun x [] tm tp) =
  let (as, endtp) = splitArrows tp in
    mapM affLinTp as >>= \ as' ->
    return (ProgFun x [] tm (joinArrows as' endtp))
affLinDefine (ProgFun _ (_ : _) _ _) =
  error "Function shouldn't have params before affine-to-linear transformation"
affLinDefine (ProgExtern _ _ (_ : _) _) =
  error "Extern shouldn't have params before affine-to-linear transformation"
affLinDefine (ProgExtern x xp [] tp) =
  let (as, endtp) = splitArrows tp in
    mapM affLinTp as >>= \ as' ->
    return (ProgExtern x xp [] (joinArrows as' tp))

-- Adds all the definitions in a file to context, after replacing arrows with Maybes
affLinDefines :: Progs -> AffLinM Ctxt
affLinDefines (Progs ps end) =
  mapM affLinDefine ps >>= \ ps' ->
  return (ctxtDefProgs (Progs ps' end))

affLinProgs :: Progs -> AffLinM Progs
affLinProgs (Progs ps end) =
  affLinDefines (Progs ps end) >>= \ g ->
  local (const g) (pure Progs <*> mapM affLinProg ps <*> affLin end)

runAffLin :: Progs -> Progs
runAffLin ps = case runRWS (affLinProgs ps) (ctxtDefProgs ps) () of
  (Progs ps' end, mtps, _) -> Progs {-(ps' ++ [ProgData (tpMaybeName i) (maybeCtors i tp) | (i, tp) <- enumerate mtps])-} ps' end

-- Make an affine file linear
affLinFile :: Progs -> Either String Progs
affLinFile = return . runAffLin
