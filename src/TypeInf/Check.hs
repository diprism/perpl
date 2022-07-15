-- Adapted from http://dev.stephendiehl.com/fun/006_hindley_milner.html
{- Code for Hindley-Milner type inference and type checking -}

module TypeInf.Check where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.RWS.Lazy
import Control.Monad.Except
import Struct.Lib
import Util.Helpers
import Scope.Fresh
import Scope.Subst
import Scope.Free
import Scope.Name
import Scope.Ctxt

-- Convention: expected type, then actual type
-- TODO: Enforce this convention
data TypeError =
    InfiniteType Var Type -- this type becomes infinite
  | UnificationError Type Type -- couldn't unify two types
  | ConflictingTypes Type Type -- expected two types to be equal, but they aren't
  | AffineError Var Term -- used more than affinely
  | ScopeError Var -- var is out of scope
  | CtorError Var -- not a constructor
  | RobustType Type -- expected type to be robust
  | NoCases -- case-of with no cases
  | ExpNonUnderscoreVar -- expected a non-"_" var
  | ExpOneNonUnderscoreVar -- expected exactly  one non-"_" var (`let <_, x, _> = ... in ...`)
  | MissingCases [Var] -- missing cases for some constructors
  | WrongNumCases Int Int -- wrong number of cases
  | WrongNumArgs Int Int -- wrong number of args, in a case (`... | Cons h t bad -> ...`)
  | MultipleDefs Var -- variable is defined multiple times
  | ExternRecData -- externs can't use recursive datatypes

instance Show TypeError where
  show (InfiniteType x tp) = "Failed to construct infinite type: " ++ x ++ " := " ++ show tp
  show (ConflictingTypes tp1 tp2) = "Conflicting types: " ++ show tp1 ++ " and " ++ show tp2
  show (AffineError x tm) = "'" ++ x ++ "' is not affine in " ++ show tm
  show (ScopeError x) = "'" ++ x ++ "' is not in scope"
  show (CtorError x) = "'" ++ x ++ "' is not a constructor"
  show (UnificationError tp1 tp2) = "Failed to unify " ++ show tp1 ++ " and " ++ show tp2
  show (RobustType tp) = "Expected " ++ show tp ++ " to be a robust type (or if binding a var, it is used non-affinely)"
  show NoCases = "Can't have case-of with no cases"
  show ExpNonUnderscoreVar = "Expected non-underscore variable here"
  show ExpOneNonUnderscoreVar = "Expected exactly one non-underscore variable"
  show (MissingCases xs) = "Missing cases: " ++ delimitWith ", " xs
  show (WrongNumCases exp act) = "Expected " ++ show exp ++ " cases, but got " ++ show act
  show (WrongNumArgs exp act) = "Expected " ++ show exp ++ " args, but got " ++ show act
  show (MultipleDefs x) = "Multiple definitions of " ++ show x
  show ExternRecData = "Extern cannot use recursive datatypes"


{- ===== Constraints ===== -}
data Constraint = Unify Type Type | Robust Type
  deriving Show

-- Discards Robust constraints
getUnifications :: [(Constraint, Loc)] -> [(Type, Type, Loc)]
getUnifications [] = []
getUnifications ((Unify tp1 tp2, l) : cs) = (tp1, tp2, l) : getUnifications cs
getUnifications (_ : cs) = getUnifications cs

constrain :: Constraint -> CheckM ()
constrain c = askLoc >>= \ loc -> tell [(c, loc)]

constrainIf :: Bool -> Constraint -> CheckM ()
constrainIf True c = constrain c
constrainIf False c = okay

instance Substitutable Constraint where
  substM (Unify tp1 tp2) = pure Unify <*> substM tp1 <*> substM tp2
  substM (Robust tp) = pure Robust <*> substM tp

  freeVars (Unify tp1 tp2) = Map.union (freeVars tp1) (freeVars tp2)
  freeVars (Robust tp) = freeVars tp

{- ===== CheckM Monad =====-}
-- Environment, stores info about vars in scope
data Env = Env { typeEnv :: Map Var ([Var], [Var], [Ctor]),
                 localEnv :: Map Var Type,
                 globalEnv :: Map Var (GlobalVar, Scheme) }

type SolveVars = Map Var IsTag

-- Proxy for location, storing the current definition we're inside and the current expression
data Loc = Loc { curDef :: String, curExpr :: String }

instance Show Loc where
  show l = delimitWith ", " ((if null (curDef l) then [] else ["in the definition " ++ curDef l]) ++ (if null (curExpr l) then [] else ["in the expression " ++ curExpr l]))

-- Reader part of the RWST monad for inference/checking
data CheckR = CheckR { checkEnv :: Env, checkLoc :: Loc }

-- Temporarily modifies the env
modifyEnv :: (Env -> Env) -> CheckR -> CheckR
modifyEnv f cr = cr { checkEnv = f (checkEnv cr) }

-- Adds a type definition to env
typeEnvInsert :: Var -> [Var] -> [Var] -> [Ctor] -> CheckR -> CheckR
typeEnvInsert y tgs ps cs = modifyEnv $ \ e -> e { typeEnv = Map.insert y (tgs, ps, cs) (typeEnv e) }

-- Adds a local var binding to the env
localEnvInsert :: Var -> Type -> CheckR -> CheckR
localEnvInsert x tp = modifyEnv $ \ e -> e { localEnv = Map.insert x tp (localEnv e) }

-- Adds a global def to the env
globalEnvInsert :: Var -> GlobalVar -> Scheme -> CheckR -> CheckR
globalEnvInsert x gv stp = modifyEnv $ \ e -> e { globalEnv = Map.insert x (gv, stp) (globalEnv e) }

-- RWST (Reader-Writer-State-Transformer) monad:
-- R (downwards): CheckR, the environment and current location
-- W (upwards): constraints and the location where they were introduced
-- S (up+down): SolveVars, the set of type vars to solve
-- T (value monad): Except, which is just a sum of a String and some other type
--                  (allows us to throw errors instead of returning a value)
type CheckM a = RWST CheckR [(Constraint, Loc)] SolveVars (Except (TypeError, Loc)) a

-- Throw an error
err :: TypeError -> CheckM a
err e = askLoc >>= \ loc -> throwError (e, loc)

-- If false, throw error e
guardM :: Bool -> TypeError -> CheckM ()
guardM True e = okay
guardM False e = err e

-- Make sure x doesn't appear in t (guards against infinite type expansions)
occursCheck :: Substitutable a => Var -> a -> Bool
occursCheck x t = x `Map.member` (freeVars t)

-- Return the env
askEnv :: CheckM Env
askEnv = checkEnv <$> ask

-- Return the current location
askLoc :: CheckM Loc
askLoc = checkLoc <$> ask

-- Modify the current location, storing a as the current def we are in
localCurDef :: Var -> CheckM b -> CheckM b
localCurDef a = local (\ cr -> cr { checkLoc = (checkLoc cr) { curDef = a } })

-- Modify the current location, storing a as the current expr we are in
localCurExpr :: Show a => a -> CheckM b -> CheckM b
localCurExpr a = local (\ cr -> cr { checkLoc = (checkLoc cr) { curExpr = show a } })

-- Add (x : tp) to env
inEnv :: Var -> Type -> CheckM a -> CheckM a
inEnv x tp = local $ localEnvInsert x tp

-- Guard against duplicate definitions of x
guardDupDef :: Var -> CheckM ()
guardDupDef x =
  askEnv >>= \ env ->
  let isdup = not (x `Map.member` typeEnv env || x `Map.member` globalEnv env) in
    guardM isdup (MultipleDefs x)

-- Checks for any duplicate definitions
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

-- Makes sure an extern's type has no recursive datatypes in it
guardExternRec :: Type -> CheckM ()
guardExternRec tp =
  askEnv >>= \ env ->
  let g = fmap (\ (tgs, ps, cs) -> DefData tgs ps cs) (typeEnv env) in
  guardM (not (isInfiniteType g tp)) ExternRecData

-- Defines a global function
defTerm :: Var -> GlobalVar -> Scheme -> CheckM a -> CheckM a
defTerm x g tp =
  local (globalEnvInsert x g tp)

-- Defines a datatype
defType :: Var -> [Var] -> [Var] -> [Ctor] -> CheckM a -> CheckM a
defType y tgs ps cs =
  local (typeEnvInsert y tgs ps cs)

-- Defines a datatype and its constructors
defData :: Var -> [Var] -> [Var] -> [Ctor] -> CheckM a -> CheckM a
defData y tgs ps cs m =
  foldr
    (\ (Ctor x tps) -> defTerm x CtorVar (Forall tgs ps (joinArrows tps (TpVar y [TpVar p [] | p <- tgs ++ ps]))))
    (defType y tgs ps cs m) cs

-- For `data List a = Nil | Cons a (List a)`, adds the type var `a` to env
defParams :: [Var] -> CheckM a -> CheckM a
defParams [] m = m
defParams (x : xs) m = defType x [] [] [] (defParams xs m)

-- Add (x1 : tp1), (x2 : tp2), ... to env
inEnvs :: [(Var, Type)] -> CheckM a -> CheckM a
inEnvs = flip $ foldr $ uncurry inEnv

-- Lookup a type variable
lookupTypeVar :: Var -> CheckM ([Var], [Var], [Ctor])
lookupTypeVar x =
  askEnv >>= \ g ->
  maybe (err (ScopeError x)) return (Map.lookup x (typeEnv g))

-- Lookup a term variable
lookupTermVar :: Var -> CheckM (Either Type (GlobalVar, Scheme))
lookupTermVar x =
  askEnv >>= \ g ->
  maybe (err (ScopeError x)) return ((Left <$> Map.lookup x (localEnv g)) |?| (Right <$> Map.lookup x (globalEnv g)))

-- Lookup the datatype that cases split on
lookupCtorType :: [CaseUs] -> CheckM (Var, [Var], [Var], [Ctor])
lookupCtorType [] = err NoCases
lookupCtorType (CaseUs x _ _ : _) =
  lookupTermVar x >>= \ tp ->
  case tp of
    Right (CtorVar, Forall _ _ ctp) -> case splitArrows ctp of
      (_, TpVar y _) -> lookupTypeVar y >>= \ (tgs, xs, cs) -> return (y, tgs, xs, cs)
      (_, etp) -> error "This shouldn't happen"
    Right (DefVar, _) -> err (CtorError x)
    Left loctp -> err (CtorError x)

-- Returns the new type vars introduced by m
listenSolveVars :: CheckM a -> CheckM (a, SolveVars)
listenSolveVars m =
  get >>= \ vs ->
  m >>= \ a ->
  get >>= \ vs' ->
  return (a, Map.difference vs' vs)

-- Returns all the vars currently in scope
boundVars :: CheckM (Map Var ())
boundVars =
  ask >>= \ d ->
  get >>= \ s ->
  let env = checkEnv d
      tpe = typeEnv env
      lce = localEnv env
      gbe = globalEnv env in
  return (Map.unions [const () <$> tpe, const () <$> lce, const () <$> gbe, const () <$> s])

-- Returns if x is a tag variable
isTag :: Var -> CheckM Bool
isTag x =
  get >>= \ s ->
  return (s Map.! x)

-- Returns a fresh var that doesn't collide with any in scope
fresh :: Var -> CheckM Var
fresh x = newVar x <$> boundVars

-- Returns a new type var (to solve) that doesn't collide with any in scope
freshTpVar' :: IsTag -> CheckM Var
freshTpVar' tg =
  fresh (if tg then "#0" else "?0") >>= \ x ->
  modify (Map.insert x tg) >>
  return x

-- Wraps TpVar around freshTpVar'
freshTp' :: Bool -> CheckM Type
freshTp' tg = pure TpVar <*> freshTpVar' tg <*> pure []

freshTpVar = freshTpVar' False
freshTagVar = freshTpVar' True
freshTp = freshTp' False
freshTag = freshTp' True

-- If NoTp, return a fresh type to solve; otherwise, check the type
annTp :: Type -> CheckM Type
annTp NoTp = freshTp
annTp tp = checkType tp

-- Ensures that a type is well-kinded (so no `List Bool Bool`, or use of undefined vars)
checkType :: Type -> CheckM Type
checkType (TpArr tp1 tp2) =
  pure TpArr <*> checkType tp1 <*> checkType tp2
checkType (TpVar y as) =
  lookupTypeVar y >>= \ (tgs, ps, _) ->
  mapM checkType as >>= \ as' ->
  mapM (const freshTag) tgs >>= \ tgs' ->
  guardM (length ps == length as) (WrongNumArgs (length ps) (length as)) >>
  pure (TpVar y (tgs' ++ as'))
checkType (TpProd am tps) =
  pure (TpProd am) <*> mapM checkType tps
checkType NoTp =
  error "checkType should never see a NoTp!"

-- Wrapper around infer', updating the current expr we are in (for better error messages)
infer :: UsTm -> CheckM Term
infer tm = localCurExpr tm (infer' tm)

-- Infers/checks a term, elaborating it from a user-term (UsTm) to a full Term
infer' :: UsTm -> CheckM Term

infer' (UsVar x) =
  -- Disable use of "_"
  guardM (x /= "_") ExpNonUnderscoreVar >>
  -- Lookup the type of x
  lookupTermVar x >>= \ etp ->
  case etp of
    -- if x is a local var:
    Left tp -> return (TmVarL x tp)
    -- if x is a global var:
    Right (gv, Forall tgs tis tp) ->
      -- pick new tags
      mapM (const freshTag) tgs >>= \ tgs' ->
      -- pick new type vars
      mapM (const freshTp) tis >>= \ tis' ->
      -- substitute old tags/type vars for new ones
      let tp' = subst (Map.fromList (zip (tgs ++ tis) (SubTp <$> (tgs' ++ tis')))) tp in
        return (TmVarG gv x (tgs' ++ tis') [] tp')

infer' (UsLam x xtp tm) =
  -- Check the annotation xtp
  annTp xtp >>= \ xtp' ->
  inEnv x xtp' (infer tm) >>= \ tm' ->
  -- If x is used more than affinely (2+ times) in tm, constrain xtp' to be robust
  constrainIf (not $ isAff x tm) (Robust xtp') >>
  return (TmLam x xtp' tm' (typeof tm'))

infer' (UsApp tm1 tm2) =
  infer tm1 >>= \ tm1' ->
  infer tm2 >>= \ tm2' ->
  -- itp = return type
  freshTp >>= \ itp ->
  -- Constraint: (typeof tm1') = (typeof tm2' -> itp)
  constrain (Unify (typeof tm1') (TpArr (typeof tm2') itp)) >>
  return (TmApp tm1' tm2' (typeof tm2') itp)

infer' (UsCase tm cs) =
  -- Lookup the datatype we have cases for
  lookupCtorType cs >>= \ (y, tgs, ps, ctors) ->
  -- Pick fresh tags and type vars
  mapM (const freshTag) tgs >>= \ itgs ->
  mapM (const freshTp) ps >>= \ ips ->
  let -- substitute old tags/type vars for new
      psub = Map.fromList (zip (tgs ++ ps) [SubTp p' | p' <- itgs ++ ips])
      -- Sort cases
      cs' = sortCases ctors (subst psub cs)
      -- Substitute old tags/type vars for new in constructors
      ctors' = subst psub ctors
      -- missing cases = ctors - cases
      missingCases = listDifference [y | (Ctor y _) <- ctors] [x | (CaseUs x _ _) <- cs] in
  -- guard against missing cases
  guardM (null missingCases) (MissingCases missingCases) >>
  -- guard against wrong number of cases
  guardM (length ctors == length cs) (WrongNumCases (length ctors) (length cs)) >>
  infer tm >>= \ tm' ->
  -- Constraint: (y itgs ips) = (typeof tm')
  constrain (Unify (TpVar y (itgs ++ ips)) (typeof tm')) >>
  -- itp = cases return type
  freshTp >>= \ itp ->
  -- infer cases
  mapM (uncurry inferCase) (zip cs' ctors') >>= \ cs'' ->
  -- Constraints: for each case `| x ps -> tm`, itp = (typeof tm)
  mapM (\ (Case x ps tm) -> constrain (Unify itp (typeof tm))) cs'' >>
  return (TmCase tm' (y, itgs ++ ips) cs'' itp)

infer' (UsIf tm1 tm2 tm3) =
  infer tm1 >>= \ tm1' ->
  infer tm2 >>= \ tm2' ->
  infer tm3 >>= \ tm3' ->
  -- Constraint: Bool = (typeof tm1')
  constrain (Unify tpBool (typeof tm1')) >>
  -- Constraint: (typeof tm2') = (typeof tm3')
  constrain (Unify (typeof tm2') (typeof tm3')) >>
  -- Translate if-then-else to case-of
  return (TmCase tm1' (tpBoolName, []) [Case tmFalseName [] tm3', Case tmTrueName [] tm2'] (typeof tm2'))

infer' (UsTmBool b) =
  -- Translate True/False into a constructor var
  return (TmVarG CtorVar (if b then "True" else "False") [] [] (TpVar "Bool" []))

infer' (UsLet x xtm tm) =
  -- Check the annotation xtp'
  --annTp xtp >>= \ xtp' ->
  infer xtm >>= \ xtm' ->
  -- Constraint: xtp' = (typeof xtm')
  --constrain (Unify xtp' (typeof xtm')) >>
  let xtp' = typeof xtm' in
  -- If x is used more than affinely (2+ times), constrain xtp' to be robust
  constrainIf (not $ isAff x tm) (Robust xtp') >>
  inEnv x xtp' (infer tm) >>= \ tm' ->
  return (TmLet x xtm' (typeof xtm') tm' (typeof tm'))

infer' (UsAmb tms) =
  mapM infer tms >>= \ tms' ->
  -- itp = type of all the terms
  freshTp >>= \ itp ->
  -- Constraint: for each tm in tms', itp = (typeof tm)
  mapM (constrain . Unify itp . typeof) tms' >>
  return (TmAmb tms' itp)

infer' (UsFactor wt tm) =
  infer tm >>= \ tm' -> return (TmFactor wt tm' (typeof tm'))

infer' (UsFail tp) =
  annTp tp >>= \ tp' ->
  return (TmAmb [] tp')

infer' (UsProd am tms) =
  mapM infer tms >>= \ tms' ->
  return (TmProd am [(tm, typeof tm) | tm <- tms'])

infer' (UsElimProd am ptm xs tm) =
  infer ptm >>= \ ptm' ->
  -- Guard against `let <x, y, _> = ... in ...` (also against `let <_, _, _> = ... in ...`)
  guardM (am /= Additive || 1 == length (filter (/= "_") xs)) ExpOneNonUnderscoreVar >>
  -- Pick a fresh type var for each x in xs
  mapM (\ x -> (,) x <$> freshTp) xs >>= \ ps ->
  -- For each (x : tp) in ps, if x is used more than affinely, constrain tp to be robust
  mapM (\ (x, tp) -> constrainIf (not $ isAff x tm) (Robust tp)) ps >>
  -- Constraint: (typeof ptm') = (ps1 */& ps2 */& ... */& psn)
  constrain (Unify (typeof ptm') (TpProd am (snds ps))) >>
  inEnvs ps (infer tm) >>= \ tm' ->
  return (TmElimProd am ptm' ps tm' (typeof tm'))

infer' (UsEqs tms) =
  mapM infer tms >>= \ tms' ->
  -- itp = type of all the tms
  freshTp >>= \ itp ->
  -- Constraint: for each tm in tms', itp = (typeof tm)
  mapM (constrain . Unify itp . typeof) tms' >>
  -- Constraint: itp is robust (can't be done naively for rec datatypes)
  -- TODO: would this work for arrow types though?
  constrain (Robust itp) >>
  return (TmEqs tms')

inferCase :: CaseUs -> Ctor -> CheckM Case
inferCase (CaseUs x xs tm) (Ctor x' ps) =
  -- Set the current expression to be the case `| x xs -> tm`
  localCurExpr (CaseUs x xs tm) $
  -- Guard against mismatched cases (probably gets caught earlier, in infer' (UsCase tm cs))
  guardM (x == x') (MissingCases [x']) >>
  -- Guard against wrong number of args
  guardM (length ps == length xs) (WrongNumArgs (length ps) (length xs)) >>
  let xps = zip xs ps in
  -- For each (x : tp) in xps, if x is used more than affinely in tm, constrain tp to be robust
  mapM (\ (x, tp) -> constrainIf (not $ isAff x tm) (Robust tp)) xps >>
  inEnvs xps (infer tm) >>= \ tm' ->
  return (Case x xps tm')
