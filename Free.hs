module Free where
import Exprs
import Ctxt
import qualified Data.Map as Map

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
renameTerm :: UsTm -> RenameM UsTm
renameTerm (UsVar x) =
  pure UsVar <*> getVar x
renameTerm (UsLam x tp tm) =
  bindVar x $ pure (flip UsLam) <*> renameType tp <*> newVar x <*> renameTerm tm
renameTerm (UsApp tm1 tm2) =
  pure UsApp <*> renameTerm tm1 <*> renameTerm tm2
renameTerm (UsCase tm cs) =
  pure UsCase
    <*> renameTerm tm
    <*> foldr (\ c cs' -> pure (:) <*> renameCase c <*> cs') (return []) cs
renameTerm (UsSamp d tp) =
  pure (UsSamp d) <*> renameType tp

-- Alpha-rename a user-case
renameCase :: CaseUs -> RenameM CaseUs
renameCase (CaseUs x as tm) =
  bindVars as $
  pure (CaseUs x)
    <*> foldr (\ a as' -> pure (:) <*> newVar a <*> as') (return []) as
    <*> renameTerm tm

-- Alpha-rename a type
renameType :: Type -> RenameM Type
renameType (TpVar y) = pure TpVar <*> getVar y
renameType (TpArr tp1 tp2) = pure TpArr <*> renameType tp1 <*> renameType tp2

-- Alpha-rename a constructor definition
renameCtor :: Ctor -> RenameM Ctor
renameCtor (Ctor x tps) = pure (Ctor x) <*> foldr (\ tp tps' -> pure (:) <*> renameType tp <*> tps') (return []) tps

-- Alpha-rename an entire user-program
renameProgs :: UsProgs -> RenameM UsProgs
renameProgs (UsProgExec tm) = pure UsProgExec <*> renameTerm tm
renameProgs (UsProgFun x tp tm ps) = pure (UsProgFun x) <*> renameType tp <*> renameTerm tm <*> renameProgs ps
renameProgs (UsProgExtern x tp ps) = pure (UsProgExtern x) <*> renameType tp <*> renameProgs ps
renameProgs (UsProgData y cs ps) = pure (UsProgData y) <*> foldr (\ c cs' -> pure (:) <*> renameCtor c <*> cs') (return []) cs <*> renameProgs ps

-- Alpha-rename a file
alphaRename :: Ctxt -> UsProgs -> UsProgs
alphaRename g ps =
  let xs = Map.mapWithKey const g
      (RenameM f) = renameProgs ps
      (ps', xs') = f xs in
    ps'
