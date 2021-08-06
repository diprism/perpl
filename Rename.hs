module Rename where
import Data.Char
import qualified Control.Monad.State.Lazy as State
import qualified Data.Map as Map
import Ctxt
import Exprs


{- ====== Alpha-Renaming Functions ====== -}
-- These function rename all bound variables
-- to unique names that don't occur anywhere
-- else in the entire program.

data SubTo tm = SubVar Var | SubTm tm | SubTp Type

type VarMap tm = Map.Map Var (SubTo tm)
--newtype RenameM' tm a = RenameM (VarMap tm -> (a, VarMap tm))
type RenameM' tm a = State.State (VarMap tm) a
type RenameM a = RenameM' Term a
type RenameUsM a = RenameM' UsTm a

data SplitVar = SplitVar String Int String
succSplitVar (SplitVar pre i suf) = SplitVar pre (succ i) suf
instance Show SplitVar where
  show (SplitVar pre i suf) = pre ++ show i ++ suf

-- Splits abc14'' into SplitVar "abc" 14 "\'\'"
splitVar :: Var -> SplitVar
splitVar x =
  let (pre, i, suf) = h True (reverse x)
      pre' = reverse pre
      i' = reverse i
      suf' = reverse suf
      i'' = if null i' then 0 else succ (read i' :: Int)
  in
    SplitVar pre' i'' suf'
  where
    h :: Bool -> String -> (String, String, String)
    h b "" = ("", "", "")
    h True ('\'' : cs) =
      let (pre, i, suf) = h True cs in
        (pre, i, '\'' : suf)
    h True (c : cs) = h False (c : cs)
    h False (c : cs)
      | isDigit c =
        let (pre, i, suf) = h False cs in
          (pre, c : i, suf)
      | otherwise = (c : cs, "", "")

newVar' :: Var -> Map.Map Var a -> Var
newVar' x xs = if Map.member x xs then h xs (splitVar x) else x
  where
    h xs x = let x' = show x in if Map.member x' xs then h xs (succSplitVar x) else x'

-- Pick a new name, if necessary
newVar :: Var -> RenameM' tm Var
newVar x = State.get >>= return . newVar' x

ctxtToTermMap :: Ctxt -> VarMap Term
ctxtToTermMap = Map.mapWithKey $ \ x d -> SubVar x

ctxtToUsTmMap :: Ctxt -> VarMap UsTm
ctxtToUsTmMap = Map.mapWithKey $ \ x d -> SubVar x

freshVar :: Ctxt -> Var -> Var
freshVar g x = fst $ State.runState (newVar x) (ctxtToUsTmMap g)


-- Lookup x in the renaming map
lookupTerm :: Var -> (Var -> tm) -> RenameM' tm tm
lookupTerm x elsetm = State.get >>= \ xs -> return (case Map.lookup x xs of { Just (SubTm tm) -> tm; Just (SubVar x') -> elsetm x'; _ -> elsetm x })
lookupType :: Var -> (Var -> Type) -> RenameM' tm Type
lookupType x elsetp = State.get >>= \ xs -> return (case Map.lookup x xs of { Just (SubTp tp) -> tp; Just (SubVar x') -> elsetp x'; _ -> elsetp x })

bindTwo :: Ord k => k -> k -> v -> Map.Map k v -> Map.Map k v
bindTwo k1 k2 v = Map.insert k1 v . Map.insert k2 v

bindVar' :: Var -> Type -> (Var -> Type -> RenameM' tm a) -> RenameM' tm a
bindVar' x tp f = renameType tp >>= bindVar x . flip f

bindVar :: Var -> (Var -> RenameM' tm a) -> RenameM' tm a
bindVar x f =
  newVar x >>= \ x' ->
  State.get >>= \ xs ->
  let ox = Map.lookup x xs in
    State.modify (bindTwo x x' (SubVar x')) >>
    f x' >>= \ a ->
    State.modify (maybe id (Map.insert x) ox) >>
    return a

--bindTpVar :: Var -> (Var -> RenameM' tm a) -> RenameM' tm a
--bindTpVar x f = newVar x >>= \ x' -> local (bindTwo x x' (Right (TpVar x'))) (f x')

bindVars :: [Param] -> ([Param] -> RenameM a) -> RenameM a
bindVars [] f = f []
bindVars ((x, tp) : ps) f =
  bindVar' x tp $ \ x' tp' ->
  bindVars ps (\ ps -> f ((x', tp') : ps))

bindUsVars :: [Var] -> ([Var] -> RenameUsM a) -> RenameUsM a
bindUsVars [] f = f []
bindUsVars (x : ps) f =
  bindVar x $ \ x' ->
  bindUsVars ps (\ ps -> f (x' : ps))

-- Alpha-rename a user-term
renameUsTm :: UsTm -> RenameUsM UsTm
renameUsTm (UsVar x) = lookupTerm x UsVar
renameUsTm (UsLam x tp tm) =
  renameType tp >>= \ tp' ->
  bindVar x $ \ x' -> pure (UsLam x' tp') <*> renameUsTm tm
renameUsTm (UsApp tm1 tm2) =
  pure UsApp <*> renameUsTm tm1 <*> renameUsTm tm2
renameUsTm (UsCase tm cs) =
  pure UsCase
    <*> renameUsTm tm
    <*> mapM renameCaseUs cs
renameUsTm (UsSamp d tp) =
  pure (UsSamp d) <*> renameType tp
renameUsTm (UsLet x xtm tm) =
  renameUsTm xtm >>= \ xtm' ->
  bindVar x $ \ x' -> pure (UsLet x' xtm') <*> renameUsTm tm

-- Alpha-rename a term
-- Note that this does NOT allow you to substitute global term vars (defines / ctors)
renameTerm :: Term -> RenameM Term
renameTerm (TmVarL x tp) =
  renameType tp >>= \ tp' ->
  lookupTerm x (flip TmVarL tp')
renameTerm (TmVarG gv x as y) =
  pure (TmVarG gv x) <*> renameArgs as <*> renameType y
renameTerm (TmLam x tp1 tm tp2) =
  bindVar' x tp1 (\ x' tp1' -> pure (TmLam x' tp1') <*> renameTerm tm) <*> renameType tp2
renameTerm (TmApp tm1 tm2 tp2 tp) =
  pure TmApp <*> renameTerm tm1 <*> renameTerm tm2 <*> renameType tp2 <*> renameType tp
renameTerm (TmLet x xtm xtp tm tp) =
  renameTerm xtm >>= \ xtm' ->
  bindVar' x xtp (\ x' xtp' -> pure (TmLet x' xtm' xtp') <*> renameTerm tm) <*> renameType tp
renameTerm (TmCase tm y cs tp) =
  pure TmCase <*> renameTerm tm <*> renameType y <*> mapM renameCase cs <*> renameType tp
renameTerm (TmSamp d tp) =
  pure (TmSamp d) <*> renameType tp

-- Alpha-rename an arg, given a function that alpha-renames its value
renameArg' :: (a -> RenameM a) -> (a, Type) -> RenameM (a, Type)
renameArg' f (a, atp) = pure (,) <*> f a <*> renameType atp
renameArgs = mapM (renameArg' renameTerm)
--renameParams = mapM (renameArg' newVar)

-- Alpha-rename a case
renameCase :: Case -> RenameM Case
renameCase (Case x ps tm) =
  bindVars ps $ \ ps' -> pure (Case x ps') <*> renameTerm tm

-- Alpha-rename a user-case
renameCaseUs :: CaseUs -> RenameUsM CaseUs
renameCaseUs (CaseUs x ps tm) =
  bindUsVars ps $ \ ps' -> pure (CaseUs x ps') <*> renameUsTm tm

-- Alpha-rename a type
renameType :: Type -> RenameM' tm Type
renameType (TpVar y) = lookupType y TpVar
renameType (TpArr tp1 tp2) = pure TpArr <*> renameType tp1 <*> renameType tp2
renameType (TpMaybe tp) = pure TpMaybe <*> renameType tp
renameType TpBool = pure TpBool

-- Alpha-rename a constructor definition
renameCtor :: Ctor -> RenameM' tm Ctor
renameCtor (Ctor x tps) = pure (Ctor x) <*> mapM renameType tps

-- Alpha-rename an entire user-program
renameUsProgs :: UsProgs -> RenameUsM UsProgs
renameUsProgs (UsProgExec tm) = pure UsProgExec <*> renameUsTm tm
renameUsProgs (UsProgFun x tp tm ps) = pure (UsProgFun x) <*> renameType tp <*> renameUsTm tm <*> renameUsProgs ps
renameUsProgs (UsProgExtern x tp ps) = pure (UsProgExtern x) <*> renameType tp <*> renameUsProgs ps
renameUsProgs (UsProgData y cs ps) = pure (UsProgData y) <*> mapM renameCtor cs <*> renameUsProgs ps

renameProg :: Prog -> RenameM Prog
renameProg (ProgFun x ps tm tp) = bindVars ps (\ ps' -> pure (ProgFun x ps') <*> renameTerm tm) <*> renameType tp
renameProg (ProgExtern x xp ps tp) = pure (ProgExtern x) <*> bindVar xp return <*> mapM renameType ps <*> renameType tp
renameProg (ProgData y cs) = pure (ProgData y) <*> mapM renameCtor cs

renameProgs :: Progs -> RenameM Progs
renameProgs (Progs ps tm) = pure Progs <*> mapM renameProg ps <*> renameTerm tm

-- Auxiliary helper
alphaRename :: Ctxt -> RenameM a -> a
alphaRename g m = fst $ State.runState m $ ctxtToTermMap g

alphaRenameUs :: Ctxt -> RenameUsM a -> a
alphaRenameUs g m = fst $ State.runState m $ ctxtToUsTmMap g

-- Alpha-rename a raw file
alphaRenameUsFile :: UsProgs -> Either String UsProgs
alphaRenameUsFile ps = return (alphaRenameUs (ctxtDefUsProgs ps) (renameUsProgs ps))

-- Alpha-rename an elaborated file
alphaRenameFile :: Progs -> Either String Progs
alphaRenameFile ps = return (alphaRename (ctxtDefProgs ps) (renameProgs ps))

-- Rename all occurrences of xi to xf in something
substs :: Ctxt -> [(Var, Either Term Type)] -> RenameM a -> a
substs g subs m = fst $ State.runState m $ foldr (uncurry Map.insert) (ctxtToTermMap g) $ map (fmap (either SubTm SubTp)) subs

-- Rename all occurrences of xi to xf in a type
substType :: Var -> Var -> Type -> Type
substType xi xf (TpVar y) = TpVar (if xi == y then xf else y)
substType xi xf (TpArr tp1 tp2) = TpArr (substType xi xf tp1) (substType xi xf tp2)
substType xi xf (TpMaybe tp) = TpMaybe (substType xi xf tp)
substType xi xf TpBool = TpBool
