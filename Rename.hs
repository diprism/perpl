module Rename where
import Data.Char
import qualified Data.Map as Map
import Ctxt
import Exprs


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
renameTerm (TmVarL x tp) =
  pure TmVarL <*> getVar x <*> renameType tp
renameTerm (TmVarG gv x as y) =
  pure (TmVarG gv) <*> getVar x <*> mapM (renameArg renameTerm) as <*> renameType y
renameTerm (TmLam x tp tm tp') =
  bindVar x (pure (flip TmLam) <*> renameType tp <*> newVar x <*> renameTerm tm) <*> renameType tp'
renameTerm (TmApp tm1 tm2 tp2 tp) =
  pure TmApp <*> renameTerm tm1 <*> renameTerm tm2 <*> renameType tp2 <*> renameType tp
renameTerm (TmLet x xtm xtp tm tp) =
  bindVar x (pure (\ x tm tp xtm xtp -> TmLet x xtm xtp tm tp) <*> newVar x <*> renameTerm tm <*> renameType tp) <*> renameTerm xtm <*> renameType xtp
renameTerm (TmCase tm y cs tp) =
  pure TmCase <*> renameTerm tm <*> renameType y <*> mapM renameCase cs <*> renameType tp
renameTerm (TmSamp d tp) =
  pure (TmSamp d) <*> renameType tp
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
renameCtor (Ctor x tps) = pure (Ctor x) <*> mapM renameType tps

-- Alpha-rename an entire user-program
renameUsProgs :: UsProgs -> RenameM UsProgs
renameUsProgs (UsProgExec tm) = pure UsProgExec <*> renameUsTm tm
renameUsProgs (UsProgFun x tp tm ps) = pure (UsProgFun x) <*> renameType tp <*> renameUsTm tm <*> renameUsProgs ps
renameUsProgs (UsProgExtern x tp ps) = pure (UsProgExtern x) <*> renameType tp <*> renameUsProgs ps
renameUsProgs (UsProgData y cs ps) = pure (UsProgData y) <*> mapM renameCtor cs <*> renameUsProgs ps

renameProg :: Prog -> RenameM Prog
renameProg (ProgFun x ps tm tp) = bindVars (map fst ps) $ pure (ProgFun x) <*> mapM (renameArg newVar) ps <*> renameTerm tm <*> renameType tp
renameProg (ProgExtern x xp ps tp) = pure (ProgExtern x) <*> (bindVar xp $ newVar xp) <*> mapM renameType ps <*> renameType tp
renameProg (ProgData y cs) = pure (ProgData y) <*> mapM renameCtor cs

renameProgs :: Progs -> RenameM Progs
renameProgs (Progs ps tm) = pure Progs <*> mapM renameProg ps <*> renameTerm tm

-- Auxiliary helper
alphaRename' :: Ctxt -> RenameM a -> a
alphaRename' g (RenameM f) = fst $ f $ Map.mapWithKey const g

-- Alpha-rename a raw file
alphaRenameUsFile :: UsProgs -> UsProgs
alphaRenameUsFile ps = alphaRename' (ctxtDefUsProgs ps) (renameUsProgs ps)

-- Alpha-rename an elaborated file
alphaRenameFile :: Progs -> Progs
alphaRenameFile ps = alphaRename' (ctxtDefProgs ps) (renameProgs ps)
