module Free where
import Exprs
import Ctxt
import Util
import qualified Data.Map as Map
import Data.List
import Data.Char

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
freeVars (UsLet x tm tm') = Map.unionWith max (freeVars tm) (Map.delete x $ freeVars tm')

freeVars' :: Term -> Map.Map Var Type
freeVars' (TmVar x tp sc) = if sc == ScopeLocal then Map.singleton x tp else Map.empty
freeVars' (TmLam x tp tm tp') = Map.delete x $ freeVars' tm
freeVars' (TmApp tm1 tm2 tp2 tp) = Map.union (freeVars' tm1) (freeVars' tm2)
freeVars' (TmCase tm tp cs tp') = foldr (Map.union . freeVarsCase') (freeVars' tm) cs
freeVars' (TmSamp d tp) = Map.empty
freeVars' (TmCtor x as tp) = Map.unions (map (freeVars' . fst) as)
freeVars' (TmFold fuf tm tp) = freeVars' tm

freeVarsCase :: CaseUs -> Map.Map Var Int
freeVarsCase (CaseUs c xs tm) = foldr Map.delete (freeVars tm) xs

freeVarsCase' :: Case -> Map.Map Var Type
freeVarsCase' (Case c as tm) = foldr (Map.delete . fst) (freeVars' tm) as


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
  h (UsLet x' tm tm') =
    if x == x' then h tm else linIf' (h tm) (linIf' (h tm') LinErr LinYes) (h tm')


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
  var2num :: Var -> Integer
  var2num n = if null n then 0 else read n :: Integer
  -- Pulls the number suffix from a var, and returns it + 1. Ex: "foo123" -> ("foo", 124)
  pullNum :: Var -> (Var, Integer)
  pullNum = fmap succ . either id (\ n -> ("", var2num n)) . foldr (\ c -> either (\ (p, s) -> Left (c : p, s)) (\ n -> if isDigit c then Right (c : n) else Left ([c], var2num n))) (Right "")
  
  h xs x n =
    let x' = x ++ show n in
      if Map.member x' xs
        then h xs x (succ n)
        else x'
  newVarH xs x =
    if Map.member x xs then uncurry (h xs) (pullNum x) else x

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
    <*> mapM renameCaseUs cs
renameUsTm (UsSamp d tp) =
  pure (UsSamp d) <*> renameType tp
renameUsTm (UsLet x tm tm') =
  bindVar x $ pure (flip UsLet) <*> renameUsTm tm <*> newVar x <*> renameUsTm tm'

-- Alpha-rename a term
renameTerm :: Term -> RenameM Term
renameTerm (TmVar x tp sc) =
  pure TmVar <*> getVar x <*> renameType tp <*> pure sc
renameTerm (TmLam x tp tm tp') =
  bindVar x (pure (flip TmLam) <*> renameType tp <*> newVar x <*> renameTerm tm) <*> renameType tp'
renameTerm (TmApp tm1 tm2 tp2 tp) =
  pure TmApp <*> renameTerm tm1 <*> renameTerm tm2 <*> renameType tp2 <*> renameType tp
renameTerm (TmCase tm y cs tp) =
  pure TmCase <*> renameTerm tm <*> renameType y <*> mapM renameCase cs <*> renameType tp
renameTerm (TmSamp d tp) =
  pure (TmSamp d) <*> renameType tp
renameTerm (TmCtor x as y) =
  pure TmCtor <*> getVar x <*> mapM (renameArg renameTerm) as <*> renameType y
renameTerm (TmFold fuf tm tp) =
  pure (TmFold fuf) <*> renameTerm tm <*> renameType tp

-- Alpha-rename an arg, given a function that alpha-renames its value
renameArg :: (a -> RenameM a) -> (a, Type) -> RenameM (a, Type)
renameArg f (a, atp) = pure (,) <*> f a <*> renameType atp

-- Alpha-rename a case
renameCase :: Case -> RenameM Case
renameCase (Case x as tm) =
  bindVars (map fst as) $ pure Case <*> getVar x <*> mapM (renameArg newVar) as <*> renameTerm tm

-- Alpha-rename a user-case
renameCaseUs :: CaseUs -> RenameM CaseUs
renameCaseUs (CaseUs x as tm) =
  bindVars as $ pure CaseUs <*> getVar x <*> mapM newVar as <*> renameUsTm tm

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
renameUsProgs :: UsProgs -> RenameM UsProgs
renameUsProgs (UsProgExec tm) = pure UsProgExec <*> renameUsTm tm
renameUsProgs (UsProgFun x tp tm ps) = pure (UsProgFun x) <*> renameType tp <*> renameUsTm tm <*> renameUsProgs ps
renameUsProgs (UsProgExtern x tp ps) = pure (UsProgExtern x) <*> renameType tp <*> renameUsProgs ps
renameUsProgs (UsProgData y cs ps) = pure (UsProgData y) <*> mapM renameCtor cs <*> renameUsProgs ps

renameProg :: Prog -> RenameM Prog
renameProg (ProgFun x tp tm) = pure (ProgFun x) <*> renameType tp <*> renameTerm tm
renameProg (ProgExtern x xp tp) = pure (ProgExtern x) <*> (bindVar xp $ newVar xp) <*> renameType tp
renameProg (ProgData y cs) = pure (ProgData y) <*> mapM renameCtor cs

renameProgs :: Progs -> RenameM Progs
renameProgs (Progs ps tm) = pure Progs <*> mapM renameProg ps <*> renameTerm tm

-- Auxiliary helper
alphaRename' :: Ctxt -> RenameM a -> a
alphaRename' g (RenameM f) = fst $ f $ Map.mapWithKey const g

-- Alpha-rename a raw file
alphaRenameUs :: Ctxt -> UsProgs -> UsProgs
alphaRenameUs g = alphaRename' g . renameUsProgs

-- Alpha-rename an elaborated file
alphaRename :: Ctxt -> Progs -> Progs
alphaRename g = alphaRename' g . renameProgs


{- ====== Affine to Linear Functions ====== -}
-- These functions convert affine terms to
-- linear ones, where an affine term is one where
-- every bound var occurs at most once, and a
-- linear term is one where every bound var
-- occurs exactly once
type FreeVars = Map.Map Var Type

-- Uses x without changing the value or type of a term
-- For example, take x : Bool and some term tm that becomes
-- case x of false -> tm | true -> tm
discard :: Ctxt -> Var -> Type -> Term -> Term
discard g x (TpArr tp1 tp2) tm =
  error "This shouldn't happen" -- Should be TpMaybe if it is an arrow type
discard g x (TpVar y) tm = maybe2 (ctxtLookupType g y)
  (error ("In Free.hs/discard, unknown type var " ++ y))
  $ \ cs ->
      TmCase (TmVar x (TpVar y) ScopeLocal) (TpVar y)
        (map (\ (Ctor x' as) ->
                let as' = ctorGetArgs x' as in
                  Case x' as' (foldr (uncurry $ discard g) tm as'))
          cs) (getType tm)
discard g x (TpMaybe tp) tm =
  let x' = aff2linName x
      tp' = getType tm in
    tmElimMaybe (TmVar x (TpMaybe tp) ScopeLocal) tp tm
      (x', TmApp (TmApp (TmSamp DistFail (TpArr tp (TpArr tp' tp')))
                   (TmVar x' tp ScopeLocal) tp (TpArr tp' tp')) tm tp' tp') tp'
discard g x TpBool tm =
  tmIf (TmVar x TpBool ScopeLocal) tm tm (getType tm)

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
aff2linCase g (Case x as tm) =
  let (tm', fvs) = aff2linh (ctxtDeclArgs g as) tm
      -- Need to discard all "as" that do not occur free in "tm"
      tm'' = discards g (Map.difference (Map.fromList as) fvs) tm' in
    (Case x as tm'', foldr (Map.delete . fst) fvs as)

-- Make a term linear, returning the local vars that occur free in it
aff2linh :: Ctxt -> Term -> (Term, FreeVars)
aff2linh g (TmVar x tp sc) =
  let ltp = aff2linTp tp
      fvs = if sc == ScopeLocal then Map.singleton x ltp else Map.empty in
    (TmVar x ltp sc, fvs)
aff2linh g (TmLam x tp tm tp') =
  let ltp = aff2linTp tp
      ltp' = aff2linTp tp'
      (tm', fvs) = aff2linh (ctxtDeclTerm g x ltp) tm
      fvs' = Map.delete x fvs
      tm'' = if Map.member x fvs then tm' else discard g x ltp tm'
      jtm = TmCtor tmJustName
              [(TmLam x ltp tm'' ltp', TpArr ltp ltp')] (TpMaybe (TpArr ltp ltp'))
      ntm = discards g fvs'
              (TmCtor tmNothingName [] (TpMaybe (TpArr ltp ltp'))) in
    (tmIf (TmSamp DistAmb TpBool) jtm ntm (TpMaybe (TpArr ltp ltp')), fvs')
aff2linh g (TmApp tm1 tm2 tp2 tp) =
  let (tm1', fvs1) = aff2linh g tm1
      (tm2', fvs2) = aff2linh g tm2
      ltp2 = aff2linTp tp2
      ltp = aff2linTp tp
      fvs = Map.union fvs1 fvs2
      ntm = TmApp (TmSamp DistFail (TpArr ltp2 ltp)) tm2' ltp2 ltp
      jx = ctorEtaName tmJustName 0
      jtm = TmApp (TmVar jx (TpArr ltp2 ltp) ScopeLocal) tm2' ltp2 ltp in
    (tmElimMaybe tm1' (TpArr ltp2 ltp) ntm (jx, jtm) ltp, fvs)
aff2linh g (TmCase tm y cs tp) =
  let csxs = map (aff2linCase g) cs
      xsAny = Map.unions (map snd csxs)
      (tm', tmxs) = aff2linh g tm
      cs' = flip map csxs $ \ (Case x as tm', xs) -> Case x as $
                  -- Need to discard any vars that occur free in other cases, but
                  -- not in this one bc all cases must have same set of free vars
                  discards (ctxtDeclArgs g as) (Map.difference xsAny xs) tm' in
    (TmCase tm' y cs' (aff2linTp tp), Map.union xsAny tmxs)
aff2linh g (TmSamp d tp) = (TmSamp d (aff2linTp tp), Map.empty)
aff2linh g (TmCtor x as y) =
  let (as', fvss) = unzip $ flip map as $ -- No need to aff2linTp bc args can't have arrows
        \ (tm, tp) -> let (tm', xs) = aff2linh g tm in ((tm', tp), xs) in
  (TmCtor x as' y, Map.unions fvss)
aff2linh g (TmFold fuf tm tp) =
  let (tm', fvs) = aff2linh g tm in
    (TmFold fuf tm' (aff2linTp tp), fvs)

-- Makes an affine term linear
aff2lin :: Ctxt -> Term -> Term
aff2lin g tm =
  let (tm', fvs) = aff2linh g tm in
    if Map.null fvs
      then tm'
      else error ("in aff2lin, remaining free vars: " ++ show (Map.keys fvs))

-- Records an instantiation of a polymorphic type
piAppend :: Var -> [Type] -> Map.Map Var [[Type]] -> Map.Map Var [[Type]]
piAppend y tp pis = Map.insertWith (++) y [tp] pis

-- Retrieves all instantiations of polymorphic types (e.g. Maybe [...]) in a term
getPolyInstsTerm :: Map.Map Var [[Type]] -> Term -> Map.Map Var [[Type]]
getPolyInstsTerm pis (TmVar x tp sc) = getPolyInstsType pis tp
getPolyInstsTerm pis (TmLam x tp tm tp') = getPolyInstsTerm (getPolyInstsType pis tp) tm -- no need to do tp' bc tm already adds all insts
getPolyInstsTerm pis (TmApp tm1 tm2 tp2 tp) = getPolyInstsTerm (getPolyInstsTerm pis tm2) tm1
getPolyInstsTerm pis (TmCase tm y cs tp) =
  foldl (\ pis (Case x as ctm) -> getPolyInstsTerm pis ctm)
    (getPolyInstsType (getPolyInstsTerm pis tm) y) cs
getPolyInstsTerm pis (TmSamp d tp) = getPolyInstsType pis tp
getPolyInstsTerm pis (TmCtor x as tp) = foldl (\ pis (a, atp) -> getPolyInstsTerm pis a) (getPolyInstsType pis tp) as
getPolyInstsTerm pis (TmFold fuf tm tp) = getPolyInstsTerm pis tm

-- Retrives all instantiations of polymorphic types (e.g. Maybe [...]) in a type
getPolyInstsType :: Map.Map Var [[Type]] -> Type -> Map.Map Var [[Type]]
getPolyInstsType pis (TpVar y) = pis
getPolyInstsType pis (TpArr tp1 tp2) = getPolyInstsType (getPolyInstsType pis tp1) tp2
getPolyInstsType pis TpBool = piAppend tpBoolName [] pis
getPolyInstsType pis (TpMaybe tp) = piAppend tpMaybeName [tp] (getPolyInstsType pis tp)

-- Retrives all instantiations of polymorphic types (e.g. Maybe [...]) in a Prog
getPolyInstsProg :: Map.Map Var [[Type]] -> Prog -> Map.Map Var [[Type]]
getPolyInstsProg pis (ProgFun x tp tm) = getPolyInstsTerm pis tm
getPolyInstsProg pis (ProgExtern x xp tp) = getPolyInstsType pis tp
getPolyInstsProg pis (ProgData y cs) = foldl (\ pis (Ctor x as) -> foldl getPolyInstsType pis as) pis cs

getPolyInstsProgs :: Map.Map Var [[Type]] -> Progs -> Map.Map Var [[Type]]
getPolyInstsProgs pis (Progs ps tm) = Map.unionsWith (++) (getPolyInstsTerm pis tm : map (getPolyInstsProg pis) ps)

-- Retrives all instantiations of a particular polymorphic type var (e.g. Maybe [...])
getPolyInsts :: Progs -> Var -> [[Type]]
getPolyInsts ps y =
  let is = getPolyInstsProgs Map.empty ps in
    maybe [] nub (Map.lookup y is)
