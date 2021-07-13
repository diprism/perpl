module Free where
import Exprs
import Ctxt
import Util
import qualified Data.Map as Map
import Data.List

-- For checking linearity, vars can appear:
-- LinNo: not at all
-- LinYes: just once
-- LinErr: multiple times
data Lin = LinNo | LinYes | LinErr
  deriving Eq

linIf :: Lin -> a -> a -> a -> a
linIf LinYes y n e = y
linIf LinNo  y n e = n
linIf LinErr y n e = e

linIf' :: Lin -> Lin -> Lin -> Lin
linIf' i y n = linIf i y n LinErr


-- Returns a map of the free vars in a term, with the max number of occurrences
freeVars :: UsTm -> Map.Map Var Int
freeVars (UsVar x) = Map.singleton x 1
freeVars (UsLam x tp tm) = Map.delete x $ freeVars tm
freeVars (UsApp tm tm') = Map.unionWith (+) (freeVars tm) (freeVars tm')
freeVars (UsCase tm cs) = foldr (Map.unionWith max . freeVarsCase) (freeVars tm) cs
freeVars (UsSamp d tp) = Map.empty

freeVarsCase :: CaseUs -> Map.Map Var Int
freeVarsCase (CaseUs c xs tm) = foldr Map.delete (freeVars tm) xs

-- Returns the (max) number of occurrences of x in tm
freeOccurrences :: Var -> UsTm -> Int
freeOccurrences x tm = Map.findWithDefault 0 x (freeVars tm)

-- Returns if x appears free in tm
isFree :: Var -> UsTm -> Bool
isFree x tm = Map.member x (freeVars tm)

-- Returns if x occurs at most once in tm
isAff :: Var -> UsTm -> Bool
isAff x tm = freeOccurrences x tm <= 1

-- Returns if x appears exactly once in tm
isLin :: Var -> UsTm -> Bool
isLin x tm = h tm == LinYes where
  linCase :: CaseUs -> Lin
  linCase (CaseUs x' as tm') = if any ((==) x) as then LinNo else h tm'
  
  h :: UsTm -> Lin
  h (UsVar x') = if x == x' then LinYes else LinNo
  h (UsLam x' tp tm) = if x == x' then LinNo else h tm
  h (UsApp tm tm') = linIf' (h tm) (linIf' (h tm') LinErr LinYes) (h tm')
  h (UsCase tm []) = h tm
  h (UsCase tm cs) = linIf' (h tm)
    -- make sure x is not in any of the cases
    (foldr (\ c -> linIf' (linCase c) LinErr) LinYes cs)
    -- make sure x is linear in all the cases, or in none of the cases
    (foldr (\ c l -> if linCase c == l then l else LinErr) (linCase (head cs)) (tail cs))
  h (UsSamp d tp) = LinNo


{- ====== Alpha-Renaming Functions ====== -}
-- These function rename all bound variables
-- to unique names that don't occur anywhere
-- else in the entire program.

type VarMap = Map.Map Var Var
newtype RenameM a = RenameM (VarMap -> (a, VarMap))
instance Functor RenameM where
  fmap f (RenameM r) = RenameM $ \ xs -> let (a, xs') = r xs in (f a, xs')
instance Applicative RenameM where
  pure a = RenameM $ \ xs -> (a, xs)
  (RenameM fab) <*> (RenameM fa) =
    RenameM $ \ xs ->
      let (ab, xs') = fab xs
          (a, xs'') = fa xs' in
      (ab a, xs'')
instance Monad RenameM where
  (RenameM fa) >>= g = RenameM $ \ xs ->
    let (a, xs') = fa xs
        (RenameM fb) = g a in
      fb xs'

-- Lookup x in the renaming map
getVar :: Var -> RenameM Var
getVar x = RenameM $ \ xs -> (Map.findWithDefault x x xs, xs)

-- Add x->x to the renaming map
bindVar :: Var -> RenameM a -> RenameM a
bindVar x (RenameM fa) = RenameM $ \ xs ->
  let x' = Map.findWithDefault x x xs
      (a, xs') = fa xs in
    (a, Map.insert x x' xs')

-- Bind a list of vars (c.f. bindVar)
bindVars :: [Var] -> RenameM a -> RenameM a
bindVars = flip (foldr bindVar)

-- Pick a new name, if necessary
newVar :: Var -> RenameM Var
newVar x = RenameM $ \ xs ->
  let x' = newVarH xs x in
    (x', Map.insert x x' (Map.insert x' x' xs))
  where
  h xs x n =
    let x' = x ++ show n in
      if Map.member x' xs
        then h xs x (succ n)
        else x'
  newVarH xs x = if Map.member x xs then h xs x 1 else x

-- Alpha-rename a user-term
renameUsTm :: UsTm -> RenameM UsTm
renameUsTm (UsVar x) =
  pure UsVar <*> getVar x
renameUsTm (UsLam x tp tm) =
  -- flipped so that newVar x doesn't rename inside tp (future-proof)
  bindVar x $ pure (flip UsLam) <*> renameType tp <*> newVar x <*> renameUsTm tm
renameUsTm (UsApp tm1 tm2) =
  pure UsApp <*> renameUsTm tm1 <*> renameUsTm tm2
renameUsTm (UsCase tm cs) =
  pure UsCase
    <*> renameUsTm tm
    <*> foldr (\ c cs' -> pure (:) <*> renameCase c <*> cs') (return []) cs
renameUsTm (UsSamp d tp) =
  pure (UsSamp d) <*> renameType tp

-- TODO: Also rename all bound vars to fresh names after aff2lin conversion?
{-renameTerm :: Term -> RenameM Term
renameTerm (TmVar x tp sc) =
  pure TmVar <*> getVar x <*> renameType tp <*> pure sc
renameTerm (TmLam x tp tm tp') =
  bindVar x $ pure TmLam <*> newVar x <*> renameType tp <*> renameTerm tm <*> renameType tp'
renameTerm (TmApp tm1 tm2 tp2 tp) =
  pure TmApp <*> renameTerm tm1 <*> renameTerm tm2 <*> renameType tp2 <*> renameType tp
renameTerm (TmCase tm cs y tp) =
  pure TmCase <*> renameTerm tm <*> mapM renameCase cs <*> getVar y <*> renameType tp
renameTerm (TmSamp d tp) = error "TODO"
renameTerm (TmCtor x as y) = error "TODO"
renameTerm (TmMaybe mtm tp) = error "TODO"
renameTerm (TmElimMaybe tm tp ntm (jx, jtm) tp') = error "TODO"
renameTerm (TmBool b) = error "TODO"
renameTerm (TmIf tm ttm ftm) = error "TODO"

renameSeq :: [RenameM a] -> RenameM [a]
renameSeq rs = foldr () ()-}

-- Alpha-rename a user-case
renameCase :: CaseUs -> RenameM CaseUs
renameCase (CaseUs x as tm) =
  bindVars as $
  pure (CaseUs x)
    <*> foldr (\ a as' -> pure (:) <*> newVar a <*> as') (return []) as
    <*> renameUsTm tm

-- Alpha-rename a type
renameType :: Type -> RenameM Type
renameType (TpVar y) = pure TpVar <*> getVar y
renameType (TpArr tp1 tp2) = pure TpArr <*> renameType tp1 <*> renameType tp2
renameType (TpMaybe tp) = pure TpMaybe <*> renameType tp
renameType TpBool = pure TpBool

-- Alpha-rename a constructor definition
renameCtor :: Ctor -> RenameM Ctor
renameCtor (Ctor x tps) = pure (Ctor x) <*> foldr (\ tp tps' -> pure (:) <*> renameType tp <*> tps') (return []) tps

-- Alpha-rename an entire user-program
renameProgs :: UsProgs -> RenameM UsProgs
renameProgs (UsProgExec tm) = pure UsProgExec <*> renameUsTm tm
renameProgs (UsProgFun x tp tm ps) = pure (UsProgFun x) <*> renameType tp <*> renameUsTm tm <*> renameProgs ps
renameProgs (UsProgExtern x tp ps) = pure (UsProgExtern x) <*> renameType tp <*> renameProgs ps
renameProgs (UsProgData y cs ps) = pure (UsProgData y) <*> foldr (\ c cs' -> pure (:) <*> renameCtor c <*> cs') (return []) cs <*> renameProgs ps

-- Alpha-rename a file
alphaRename :: Ctxt -> UsProgs -> UsProgs
alphaRename g ps =
  let xs = Map.mapWithKey const g
      (RenameM f) = renameProgs ps
      (ps', xs') = f xs in
    ps'



{- ====== Affine to Linear Functions ====== -}
-- These functions convert affine terms to
-- linear ones, where an affine term is one where
-- every bound var occurs at most once, and a
-- linear term is one where every bound var
-- occurs exactly once
type FreeVars = Map.Map Var Type

eliminate :: Ctxt -> Var -> Type -> Term -> Term
eliminate g x (TpArr tp1 tp2) tm =
  let tp = getType tm in
    error "This shouldn't happen"
    --tmElimMaybe (TmVar x (TpMaybe (TpArr tp1 tp2)) ScopeLocal) (TpArr tp1 tp2) tm (ctorEtaName tmJustName 0, TmSamp DistFail tp) tp
eliminate g x (TpVar y) tm = maybe2 (ctxtLookupType g y)
  (error ("In Free.hs/eliminate, unknown type var " ++ y))
  $ \ cs ->
      TmCase (TmVar x (TpVar y) ScopeLocal) (TpVar y)
        (map (\ (Ctor x' as) ->
                let as' = ctorGetArgs x' as in
                  Case x' as' (foldr (uncurry $ eliminate g) tm as'))
          cs) (getType tm)
eliminate g x (TpMaybe tp) tm =
  let x' = aff2linName x
      tp' = getType tm in
    tmElimMaybe (TmVar x (TpMaybe tp) ScopeLocal) tp tm (x', TmSamp DistFail tp') tp'
eliminate g x TpBool tm =
  tmIf (TmVar x TpBool ScopeLocal) tm tm (getType tm)

{-
L(\x:X. b) [x \in FV(b)] => \x:Maybe L'(X). case x of nothing => discard (FV(b) - {x}) in fail | just x' => L(b)
L(\x:X. b) [x \notin FV(b)] => \x:Maybe L'(X). case x of nothing => L(b) | just x' -> discard x', FV(b) in fail
L(f a) => L(f) (if amb then nothing else just L(a))

-}

eliminates :: Ctxt -> FreeVars -> Term -> Term
eliminates g fvs tm = Map.foldrWithKey (eliminate g) tm fvs

aff2linTp :: Type -> Type
aff2linTp (TpVar y) = TpVar y
aff2linTp (TpArr tp1 tp2) = TpArr (TpMaybe (aff2linTp tp1)) (aff2linTp tp2)
aff2linTp (TpMaybe tp) = TpMaybe (aff2linTp tp)
aff2linTp TpBool = TpBool

aff2linCase :: Ctxt -> Case -> (Case, FreeVars)
aff2linCase g (Case x as tm) =
  let (tm', fvs) = aff2linh (ctxtDeclArgs g as) tm
      tm'' = eliminates g (Map.difference (Map.fromList as) fvs) tm' in
    (Case x as tm'', foldr (Map.delete . fst) fvs as)

-- TODO: at fail terms we don't eliminate FVs; should we?
aff2linh :: Ctxt -> Term -> (Term, FreeVars)
aff2linh g (TmVar x tp sc) =
  let ltp = aff2linTp tp in
    (TmVar x ltp sc, if sc == ScopeLocal then Map.singleton x ltp else Map.empty)
aff2linh g (TmLam x tp tm tp') =
  let lptp = aff2linTp tp
      ltp = TpMaybe lptp
      ltp' = aff2linTp tp'
      --rtp = TpArr ltp ltp'
      (tm', fvs) = aff2linh (ctxtDeclTerm g x tp) tm
      x' = aff2linName x
      mktm = \ ntm jtm -> (TmLam x' ltp (tmElimMaybe (TmVar x' ltp ScopeLocal) lptp ntm (x, jtm) ltp') ltp', Map.delete x fvs)
      free = Map.member x fvs
      fvs' = if free then Map.delete x fvs else Map.insert x lptp fvs
      failtm = TmSamp DistFail ltp' in
    if free then mktm failtm tm' else mktm tm' failtm
aff2linh g (TmApp tm1 tm2 tp2 tp) =
  -- L(f a) => L(f) (if amb then (discard FV(a) in nothing) else just L(a))
  let (tm1', fvs1) = aff2linh g tm1
      (tm2', fvs2) = aff2linh g tm2
      ltp2 = aff2linTp tp2
      ltp = aff2linTp tp
      jx = ctorEtaName tmJustName 0 in
    (TmApp tm1' (tmIf (TmSamp DistAmb TpBool) (eliminates g fvs2 (tmMaybe Nothing ltp2)) (tmMaybe (Just tm2') ltp2) (TpMaybe ltp2)) (TpMaybe ltp2) ltp,
     Map.union fvs1 fvs2)
aff2linh g (TmCase tm y cs tp) =
  let csxs = map (aff2linCase g) cs
      xsAny = Map.unions (map snd csxs)
      xsAll = foldr Map.intersection xsAny (map snd csxs)
      (tm', tmxs) = aff2linh g tm
      cs' = flip map csxs $ \ (Case x as tm', xs) -> Case x as $
                  eliminates (ctxtDeclArgs g as) (Map.difference xsAny xs) tm' in
    (TmCase tm' y cs' (aff2linTp tp), Map.union xsAll tmxs)
aff2linh g (TmSamp d tp) = (TmSamp d (aff2linTp tp), Map.empty)
aff2linh g (TmCtor x as y) =
  let (as', fvss) = unzip $ flip map as $ -- No need to aff2linTp bc args can't have arrows
        \ (tm, tp) -> let (tm', xs) = aff2linh g tm in ((tm', tp), xs) in
  (TmCtor x as' y, Map.unions fvss)

aff2lin :: Ctxt -> Term -> Term
aff2lin g tm =
  let (tm', fvs) = aff2linh g tm in
    if Map.null fvs
      then tm'
      else error ("in aff2lin, remaining free vars: " ++ show (Map.keys fvs))


piAppend :: Var -> [Type] -> Map.Map Var [[Type]] -> Map.Map Var [[Type]]
piAppend y tp pis = Map.insertWith (++) y [tp] pis

-- Retrieves all instantiations of polymorphic types (e.g. Maybe [...])
getPolyInstsTerm :: Map.Map Var [[Type]] -> Term -> Map.Map Var [[Type]]
getPolyInstsTerm pis (TmVar x tp sc) = getPolyInstsType pis tp
getPolyInstsTerm pis (TmLam x tp tm tp') = getPolyInstsTerm (getPolyInstsType pis tp) tm -- no need to do tp' bc tm already adds all insts
getPolyInstsTerm pis (TmApp tm1 tm2 tp2 tp) = getPolyInstsTerm (getPolyInstsTerm pis tm2) tm1
getPolyInstsTerm pis (TmCase tm y cs tp) =
  foldl (\ pis (Case x as ctm) -> getPolyInstsTerm pis ctm)
    (getPolyInstsType (getPolyInstsTerm pis tm) y) cs
getPolyInstsTerm pis (TmSamp d tp) = getPolyInstsType pis tp
getPolyInstsTerm pis (TmCtor x as tp) = foldl (\ pis (a, atp) -> getPolyInstsTerm pis a) (getPolyInstsType pis tp) as

getPolyInstsType :: Map.Map Var [[Type]] -> Type -> Map.Map Var [[Type]]
getPolyInstsType pis (TpVar y) = pis
getPolyInstsType pis (TpArr tp1 tp2) = getPolyInstsType (getPolyInstsType pis tp1) tp2
getPolyInstsType pis TpBool = piAppend tpBoolName [] pis
getPolyInstsType pis (TpMaybe tp) = piAppend tpMaybeName [tp] (getPolyInstsType pis tp)

getPolyInstsProg :: Map.Map Var [[Type]] -> Progs -> Map.Map Var [[Type]]
getPolyInstsProg pis (ProgExec tm) = getPolyInstsTerm pis tm
getPolyInstsProg pis (ProgFun x tp tm ps) = getPolyInstsProg (getPolyInstsTerm pis tm) ps
getPolyInstsProg pis (ProgExtern x tp ps) = getPolyInstsProg (getPolyInstsType pis tp) ps
getPolyInstsProg pis (ProgData y cs ps) = getPolyInstsProg (foldl (\ pis (Ctor x as) -> foldl getPolyInstsType pis as) pis cs) ps

getPolyInsts :: Progs -> Var -> [[Type]]
getPolyInsts ps y =
  let is = getPolyInstsProg Map.empty ps in
    maybe [] nub (Map.lookup y is)
