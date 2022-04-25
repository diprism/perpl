-- Adapted from http://dev.stephendiehl.com/fun/006_hindley_milner.html
{- Code for Hindley-Milner type inference and type checking -}

module TypeInf.Check where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.RWS.Lazy
import Control.Monad.Except
import Exprs
import Subst
import Free
import Util.Helpers
import Name
import Show()
import Fresh

-- Convention: expected type, then actual type
-- TODO: Enforce this convention
data TypeError =
    InfiniteType Var Type
  | UnificationError Type Type
  | ConflictingTypes Type Type
  | AffineError Var Term -- used more than affinely
  | ScopeError Var
  | CtorError Var
  | RobustType Type
--  | NoInference
  | NoCases
  | ExpNonUnderscoreVar
  | ExpOneNonUnderscoreVar
  | MissingCases [Var]
  | WrongNumCases Int Int
  | WrongNumArgs Int Int
  | MultipleDefs Var

instance Show TypeError where
  show (InfiniteType x tp) = "Failed to construct infinite type: " ++ x ++ " := " ++ show tp
  show (ConflictingTypes tp1 tp2) = "Conflicting types: " ++ show tp1 ++ " and " ++ show tp2
  show (AffineError x tm) = "'" ++ x ++ "' is not affine in " ++ show tm
  show (ScopeError x) = "'" ++ x ++ "' is not in scope"
  show (CtorError x) = "'" ++ x ++ "' is not a constructor"
  show (UnificationError tp1 tp2) = "Failed to unify " ++ show tp1 ++ " and " ++ show tp2
  show (RobustType tp) = "Expected " ++ show tp ++ " to be a robust type (or if binding a var, it is used non-affinely)"
--  show NoInference = "Could not infer a type"
  show NoCases = "Can't have case-of with no cases"
  show ExpNonUnderscoreVar = "Expected non-underscore variable here"
  show ExpOneNonUnderscoreVar = "Expected exactly one non-underscore variable"
  show (MissingCases xs) = "Missing cases: " ++ delimitWith ", " xs
  show (WrongNumCases exp act) = "Expected " ++ show exp ++ " cases, but got " ++ show act
  show (WrongNumArgs exp act) = "Expected " ++ show exp ++ " args, but got " ++ show act
  show (MultipleDefs x) = "Multiple definitions of " ++ show x

data Env = Env { typeEnv :: Map Var ([Var], [Var], [Ctor]),
                 localEnv :: Map Var Type,
                 globalEnv :: Map Var (GlobalVar, Scheme) }

compose :: Subst -> Subst -> Subst
s1 `compose` s2 = Map.map (subst s1) s2 `Map.union` s1

data Constraint = Unify Type Type | Robust Type deriving Show

getUnifications :: [(Constraint, Loc)] -> [(Type, Type, Loc)]
getUnifications [] = []
getUnifications ((Unify tp1 tp2, l) : cs) = (tp1, tp2, l) : getUnifications cs
getUnifications (_ : cs) = getUnifications cs

instance Substitutable Constraint where
  substM (Unify tp1 tp2) = pure Unify <*> substM tp1 <*> substM tp2
  substM (Robust tp) = pure Robust <*> substM tp

  freeVars (Unify tp1 tp2) = Map.union (freeVars tp1) (freeVars tp2)
  freeVars (Robust tp) = freeVars tp

type SolveVars = Map Var IsTag

data Loc = Loc { curDef :: String, curExpr :: String }

instance Show Loc where
  show l = delimitWith ", " ((if null (curDef l) then [] else ["in the definition " ++ curDef l]) ++ (if null (curExpr l) then [] else ["in the expression " ++ curExpr l]))

data CheckR = CheckR { checkEnv :: Env, checkLoc :: Loc }

modifyEnv :: (Env -> Env) -> CheckR -> CheckR
modifyEnv f cr = cr { checkEnv = f (checkEnv cr) }

typeEnvInsert :: Var -> [Var] -> [Var] -> [Ctor] -> CheckR -> CheckR
typeEnvInsert y tgs ps cs = modifyEnv $ \ e -> e { typeEnv = Map.insert y (tgs, ps, cs) (typeEnv e) }

localEnvInsert :: Var -> Type -> CheckR -> CheckR
localEnvInsert x tp = modifyEnv $ \ e -> e { localEnv = Map.insert x tp (localEnv e) }

globalEnvInsert :: Var -> GlobalVar -> Scheme -> CheckR -> CheckR
globalEnvInsert x gv stp = modifyEnv $ \ e -> e { globalEnv = Map.insert x (gv, stp) (globalEnv e) }

type CheckM a = RWST CheckR [(Constraint, Loc)] SolveVars (Except (TypeError, Loc)) a

err :: TypeError -> CheckM a
err e = askLoc >>= \ loc -> throwError (e, loc)

guardM :: Bool -> TypeError -> CheckM ()
guardM True e = okay
guardM False e = err e

occursCheck :: Substitutable a => Var -> a -> Bool
occursCheck x t = x `Map.member` (freeVars t)

askEnv :: CheckM Env
askEnv = checkEnv <$> ask

askLoc :: CheckM Loc
askLoc = checkLoc <$> ask

localCurDef :: Var -> CheckM b -> CheckM b
localCurDef a = local (\ cr -> cr { checkLoc = (checkLoc cr) { curDef = a } })

localCurExpr :: Show a => a -> CheckM b -> CheckM b
localCurExpr a = local (\ cr -> cr { checkLoc = (checkLoc cr) { curExpr = show a } })

inEnv :: Var -> Type -> CheckM a -> CheckM a
inEnv x tp = local $ localEnvInsert x tp

guardDupDef :: Var -> CheckM ()
guardDupDef x =
  askEnv >>= \ env ->
  let isdup = not (x `Map.member` typeEnv env || x `Map.member` globalEnv env) in
    guardM isdup (MultipleDefs x)

anyDupDefs :: UsProgs -> CheckM ()
anyDupDefs (UsProgs ps etm) =
  either
    (err . MultipleDefs)
    (const okay)
    (foldlM h (return Set.empty) ps)
  where
    addDef :: Var -> Set Var -> Either Var (Set Var)
    addDef x xs
      | x `Set.member` xs = Left x
      | otherwise = Right (Set.insert x xs)
    
    h :: Set Var -> UsProg -> Either Var (Set Var)
    h xs (UsProgFun x atp tm) = addDef x xs
    h xs (UsProgExtern x tp) = addDef x xs
    h xs (UsProgData y ps cs) =
      foldlM (\ xs' (Ctor x tps) -> addDef x xs') (addDef y xs) cs

defTerm :: Var -> GlobalVar -> Scheme -> CheckM a -> CheckM a
defTerm x g tp =
  local (globalEnvInsert x g tp)

defType :: Var -> [Var] -> [Var] -> [Ctor] -> CheckM a -> CheckM a
defType y tgs ps cs =
  local (typeEnvInsert y tgs ps cs)

defData :: Var -> [Var] -> [Var] -> [Ctor] -> CheckM a -> CheckM a
defData y tgs ps cs m =
  foldr
    (\ (Ctor x tps) -> defTerm x CtorVar (Forall tgs ps (joinArrows tps (TpVar y [TpVar p [] | p <- tgs ++ ps]))))
    (defType y tgs ps cs m) cs

defParams :: [Var] -> CheckM a -> CheckM a
defParams [] m = m
defParams (x : xs) m = defType x [] [] [] (defParams xs m)

inEnvs :: [(Var, Type)] -> CheckM a -> CheckM a
inEnvs = flip $ foldr $ uncurry inEnv

lookupType :: Var -> CheckM ([Var], [Var], [Ctor])
lookupType x =
  askEnv >>= \ g ->
  maybe (err (ScopeError x)) return (Map.lookup x (typeEnv g))

lookupTerm :: Var -> CheckM (Either Type (GlobalVar, Scheme))
lookupTerm x =
  askEnv >>= \ g ->
  maybe (err (ScopeError x)) return ((Left <$> Map.lookup x (localEnv g)) |?| (Right <$> Map.lookup x (globalEnv g)))

lookupCtorType :: [CaseUs] -> CheckM (Var, [Var], [Var], [Ctor])
lookupCtorType [] = err NoCases
lookupCtorType (CaseUs x _ _ : _) =
  lookupTerm x >>= \ tp ->
  case tp of
    Right (CtorVar, Forall _ _ ctp) -> case splitArrows ctp of
      (_, TpVar y _) -> lookupType y >>= \ (tgs, xs, cs) -> return (y, tgs, xs, cs)
      (_, etp) -> error "This shouldn't happen"
    Right (DefVar, _) -> err (CtorError x)
    Left loctp -> err (CtorError x)

listenSolveVars :: CheckM a -> CheckM (a, SolveVars)
listenSolveVars m =
  get >>= \ vs ->
  m >>= \ a ->
  get >>= \ vs' ->
  return (a, Map.difference vs' vs)

boundVars :: CheckM (Map Var ())
boundVars =
  ask >>= \ d ->
  get >>= \ s ->
  let env = checkEnv d
      tpe = typeEnv env
      lce = localEnv env
      gbe = globalEnv env in
  return (Map.unions [const () <$> tpe, const () <$> lce, const () <$> gbe, const () <$> s])

isTag :: Var -> CheckM Bool
isTag x =
  get >>= \ s ->
  return (s Map.! x)

fresh :: Var -> CheckM Var
fresh x = newVar x <$> boundVars

freshTpVar' :: IsTag -> CheckM Var
freshTpVar' tg =
  fresh (if tg then "#0" else "?0") >>= \ x ->
  modify (Map.insert x tg) >>
  return x

freshTp' :: Bool -> CheckM Type
freshTp' tg = pure TpVar <*> freshTpVar' tg <*> pure []

freshTpVar = freshTpVar' False
freshTagVar = freshTpVar' True
freshTp = freshTp' False
freshTag = freshTp' True

annTp :: Type -> CheckM Type
annTp NoTp = freshTp
annTp tp = checkType tp

checkType :: Type -> CheckM Type
checkType (TpArr tp1 tp2) =
  pure TpArr <*> checkType tp1 <*> checkType tp2
checkType (TpVar y as) =
  lookupType y >>= \ (tgs, ps, _) ->
  mapM checkType as >>= \ as' ->
--  askEnv >>= \ g ->
--  (if isRecDatatype (fmap snd (typeEnv g)) y then (freshTag >>= \ x -> return [x]) else return []) >>= \ tg ->
  mapM (const freshTag) tgs >>= \ tgs' ->
  guardM (length ps == length as) (WrongNumArgs (length ps) (length as)) >>
  pure (TpVar y (tgs' ++ as'))
checkType (TpProd am tps) =
  pure (TpProd am) <*> mapM checkType tps
checkType NoTp =
  error "checkType should never see a NoTp!"

infixl 1 >>:
(>>:) :: CheckM Term -> (Term -> Type -> CheckM a) -> CheckM a
m >>: f = m >>= \ tm -> f tm (typeof tm)

constrain :: Constraint -> CheckM ()
constrain c = askLoc >>= \ loc -> tell [(c, loc)]

constrainIf :: Bool -> Constraint -> CheckM ()
constrainIf True c = constrain c
constrainIf False c = okay

infer :: UsTm -> CheckM Term
infer tm = localCurExpr tm (infer' tm)

infer' :: UsTm -> CheckM Term

infer' (UsVar x) =
  guardM (x /= "_") ExpNonUnderscoreVar >>
  lookupTerm x >>= \ etp ->
  case etp of
    Left tp -> return (TmVarL x tp)
    Right (gv, Forall tgs tis tp) ->
--      askEnv >>= \ g ->
      mapM (const freshTag) tgs >>= \ tgs' ->
      mapM (const freshTp) tis >>= \ tis' ->
      let tp' = subst (Map.fromList (zip (tgs ++ tis) (SubTp <$> (tgs' ++ tis')))) tp in
        return (TmVarG gv x (tgs' ++ tis') [] tp')
{-      
      let g' = fmap snd (typeEnv g)
          (_, TpVar y _) = splitArrows tp
          isrec = gv == CtorVar && isRecType g' (TpVar y []) in
        (if isrec then fmap Just freshTag else return Nothing) >>= \ tg ->
        let tg' = maybe [] (\ tgx -> [(y, SubTag tgx)]) tg
            tp' = subst (Map.fromList (tg' ++ zip tis (SubTp <$> tis'))) tp
            tis'' = maybe tis' (\ x -> TpVar x [] : tis') tg
        in
          return (TmVarG gv x tis'' [] tp')
-}

infer' (UsLam x xtp tm) =
  annTp xtp >>= \ xtp' ->
  inEnv x xtp' (infer tm) >>= \ tm' ->
  constrainIf (not $ isAff x tm) (Robust xtp') >>
  return (TmLam x xtp' tm' (typeof tm'))

infer' (UsApp tm1 tm2) =
  infer tm1 >>: \ tm1' tp1 ->
  infer tm2 >>: \ tm2' tp2 ->
  freshTp >>= \ itp ->
  --freshTp >>= \ itp1l ->
  --freshTp >>= \ itp1r ->
  constrain (Unify tp1 (TpArr tp2 itp)) >>
  return (TmApp tm1' tm2' tp2 itp)

infer' (UsCase tm cs) =
  lookupCtorType cs >>= \ (y, tgs, ps, ctors) ->
  mapM (const freshTag) tgs >>= \ itgs ->
  mapM (const freshTp) ps >>= \ ips ->
  let psub = Map.fromList (zip (tgs ++ ps) [SubTp p' | p' <- itgs ++ ips])
      cs' = sortCases ctors (subst psub cs)
      ctors' = subst psub ctors
      cs_map = Map.fromList [(x, ()) | (CaseUs x _ _) <- cs]
      ctors_map = Map.fromList [(y, ()) | (Ctor y _) <- ctors]
      missingCases = Map.difference ctors_map cs_map in
  guardM (null missingCases) (MissingCases (Map.keys missingCases)) >>
  guardM (length ctors == length cs) (WrongNumCases (length ctors) (length cs)) >>
  infer tm >>: \ tm' ytp ->
  constrain (Unify (TpVar y (itgs ++ ips)) ytp) >>
  freshTp >>= \ itp ->
--  mapM (const freshTp) ps >>= \ ips ->
  mapM (uncurry inferCase) (zip cs' ctors') >>= \ cs'' ->
  mapM (\ (Case x ps tm) -> constrain (Unify itp (typeof tm))) cs'' >>
  return (TmCase tm' (y, itgs ++ ips) cs'' itp)

infer' (UsIf tm1 tm2 tm3) =
  infer tm1 >>: \ tm1' tp1 ->
  infer tm2 >>: \ tm2' tp2 ->
  infer tm3 >>: \ tm3' tp3 ->
  constrain (Unify tpBool tp1) >>
  constrain (Unify tp2 tp3) >>
  return (TmCase tm1' (tpBoolName, []) [Case tmFalseName [] tm3', Case tmTrueName [] tm2'] tp2)

infer' (UsTmBool b) =
  return (TmVarG CtorVar (if b then "True" else "False") [] [] (TpVar "Bool" []))

infer' (UsSamp d tp) =
  annTp tp >>= \ tp' ->
  constrain (Robust tp') >>
  return (TmSamp d tp')

infer' (UsLet x xtp xtm tm) =
  annTp xtp >>= \ xtp' ->
  infer xtm >>: \ xtm' xtp'' ->
  constrain (Unify xtp' xtp'') >>
  constrainIf (not $ isAff x tm) (Robust xtp') >>
  inEnv x xtp' (infer tm) >>: \ tm' tp ->
  return (TmLet x xtm' xtp'' tm' tp)

infer' (UsAmb tms) =
  mapM infer tms >>= \ tms' ->
  freshTp >>= \ itp ->
  mapM (constrain . Unify itp . typeof) tms' >>
  return (TmAmb tms' itp)

infer' (UsProd am tms) =
  mapM infer tms >>= \ tms' ->
  return (TmProd am [(tm, typeof tm) | tm <- tms'])

infer' (UsElimProd am ptm xs tm) =
  infer ptm >>: \ ptm' ptp ->
  guardM (am == Multiplicative || 1 == length (filter (/= "_") xs)) ExpOneNonUnderscoreVar >>
  mapM (\ x -> (,) x <$> freshTp) xs >>= \ ps ->
  mapM (\ (x, tp) -> constrainIf (not $ isAff x tm) (Robust tp)) ps >>
  constrain (Unify ptp (TpProd am (snds ps))) >>
  inEnvs ps (infer tm) >>: \ tm' tp ->
  return (TmElimProd am ptm' ps tm' tp)

infer' (UsEqs tms) =
  mapM infer tms >>= \ tms' ->
  freshTp >>= \ itp ->
  mapM (constrain . Unify itp . typeof) tms' >>
  constrain (Robust itp) >>
  return (TmEqs tms')

inferCase :: CaseUs -> Ctor -> CheckM Case
inferCase (CaseUs x xs tm) (Ctor x' ps) =
  localCurExpr (CaseUs x xs tm) $
  guardM (x == x') (MissingCases [x']) >> -- probably not necessary
  guardM (length ps == length xs) (WrongNumArgs (length ps) (length xs)) >>
  let xps = zip xs ps in
  mapM (\ (x, tp) -> constrainIf (not $ isAff x tm) (Robust tp)) xps >>
  inEnvs xps (infer tm) >>= \ tm' ->
  return (Case x xps tm')
