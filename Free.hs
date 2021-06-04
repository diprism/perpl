module Free where
import Exprs
import Ctxt
import qualified Data.Map as Map

freeVars :: UsTm -> Map.Map Var Int
freeVars (UsVar x) = Map.singleton x 1
freeVars (UsLam x tp tm) = Map.delete x $ freeVars tm
freeVars (UsApp tm tm') = Map.unionWith (+) (freeVars tm) (freeVars tm')
freeVars (UsCase tm cs) = foldr (Map.unionWith max . freeVarsCase) (freeVars tm) cs
freeVars (UsSamp d y) = Map.empty -- TODO: should this return a list of y's ctors?

{-freeVars :: Term -> Map.Map Var Int
freeVars (TmVar x tp) = Map.singleton x 1
freeVars (TmLam x tp tm tp') = Map.delete x $ freeVars tm
freeVars (TmApp tm tm' tp tp') = Map.unionWith (+) (freeVars tm) (freeVars tm')
freeVars (TmCase tm cs y tp) = foldr (Map.unionWith max . freeVarsCase) (freeVars tm) cs
freeVars (TmSamp d y) = Map.empty -- TODO: should this return a list of y's ctors?

freeVarsCase :: Case -> Map.Map Var Int
freeVarsCase (Case c xs tm) = foldr Map.delete (freeVars tm) xs-}

freeVarsCase :: CaseUs -> Map.Map Var Int
freeVarsCase (CaseUs c xs tm) = foldr Map.delete (freeVars tm) xs

freeOccurrences :: Var -> UsTm -> Int
freeOccurrences x tm = Map.findWithDefault 0 x (freeVars tm)

isFree :: Var -> UsTm -> Bool
isFree x tm = Map.member x (freeVars tm)

isAff :: Var -> UsTm -> Bool
isAff x tm = freeOccurrences x tm <= 1

data Lin = LinNo | LinYes | LinErr
  deriving Eq

linIf :: Lin -> a -> a -> a -> a
linIf LinYes y n e = y
linIf LinNo  y n e = n
linIf LinErr y n e = e

linIf' :: Lin -> Lin -> Lin -> Lin
linIf' i y n = linIf i y n LinErr

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
  h (UsSamp d y) = LinNo

-- Renames bound vars to avoid shadowing
alphaRename :: Ctxt -> UsTm -> UsTm
alphaRename g tm = rename (Map.mapWithKey const g) tm where
  
  renameVar :: Map.Map Var Var -> Var -> Var
  renameVar xs x = Map.findWithDefault x x xs

  newVar :: Map.Map Var Var -> Var -> Var
  newVar xs x = if Map.member x xs then h xs x 1 else x where
    h xs x n =
      let x' = x ++ show n in
        if Map.member x' xs then h xs x (succ n) else x'

  declVar :: Map.Map Var Var -> Var -> (Map.Map Var Var, Var)
  declVar xs x =
    let x' = newVar xs x in
      (Map.insert x x' (Map.insert x' x' xs), x')
  
  rename :: Map.Map Var Var -> UsTm -> UsTm
  rename xs (UsVar x) = UsVar (renameVar xs x)
  rename xs (UsLam x tp tm) =
    let (xs', x') = declVar xs x in
      UsLam x' (renameType xs tp) (rename xs' tm)
  rename xs (UsApp tm1 tm2) = UsApp (rename xs tm1) (rename xs tm2)
  rename xs (UsCase tm cs) = UsCase (rename xs tm) (map (renameCase xs) cs)
  rename xs (UsSamp d y) = UsSamp d (renameVar xs y)

  renameCase :: Map.Map Var Var -> CaseUs -> CaseUs
  renameCase xs (CaseUs x as tm) =
    uncurry (CaseUs (renameVar xs x)) (renameCaseh xs as tm)
    
  renameCaseh :: Map.Map Var Var -> [Var] -> UsTm -> ([Var], UsTm)
  renameCaseh xs (a : as) tm =
    let (xs', a') = declVar xs a
        (as', tm') = renameCaseh xs' as tm in
      ((a' : as'), tm')
  renameCaseh xs [] tm = ([], rename xs tm)

  renameType :: Map.Map Var Var -> Type -> Type
  renameType xs (TpVar y) = TpVar (renameVar xs y)
  renameType xs (TpArr tp1 tp2) = TpArr (renameType xs tp1) (renameType xs tp2)
