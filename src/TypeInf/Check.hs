-- Adapted from http://dev.stephendiehl.com/fun/006_hindley_milner.html
{- Code for Hindley-Milner type inference and type checking -}

module TypeInf.Check where
import Data.List (intercalate)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad (replicateM)
import Control.Monad.RWS.Lazy
import Control.Monad.Except
import Struct.Lib
import Util.Helpers
import Scope.Fresh (newVar)
import Scope.Subst (Subst(tags, tpVars), FreeVars(freeTpVars), Substitutable, substM, subst, freeVars)
import Scope.Free (isAff, isInfiniteType)
import Scope.Ctxt (Ctxt(tmVars, tmNames, tpNames), CtTerm(..), CtType(..), ctxtAddLocal, ctxtAddDefine, ctxtAddExtern, ctxtAddData)

-- Convention: expected type, then actual type
-- TODO: Enforce this convention
data TypeError =
    InfiniteType TpVar Type -- this type becomes infinite
  | UnificationError Type Type -- couldn't unify two types
  | ConflictingTypes Type Type -- expected two types to be equal, but they aren't
  | AffineError TmVar Term -- used more than affinely
  | ScopeError String -- var is out of scope
  | CtorError TmName -- not a constructor
  | RobustType Type -- expected type to be robust
  | PositiveType Type -- expected type to contain no arrows or additive products
  | NoCases -- case-of with no cases
  | MissingCases [TmName] -- missing cases for some constructors
  | WrongNumCases Int Int -- wrong number of cases
  | WrongNumArgs Int Int -- wrong number of args, in a case (`... | Cons h t bad -> ...`)
  | MultipleDefs String -- variable is defined multiple times
  | ExternRecData -- externs can't use recursive datatypes

instance Show TypeError where
  show (InfiniteType x tp) = "Failed to construct infinite type: " ++ show x ++ " := " ++ show tp
  show (ConflictingTypes tp1 tp2) = "Conflicting types: " ++ show tp1 ++ " and " ++ show tp2
  show (AffineError x tm) = "'" ++ show x ++ "' is not affine in " ++ show tm
  show (ScopeError x) = "'" ++ x ++ "' is not in scope"
  show (CtorError x) = "'" ++ show x ++ "' is not a constructor"
  show (UnificationError tp1 tp2) = "Failed to unify " ++ show tp1 ++ " and " ++ show tp2
  show (RobustType tp) = "Expected " ++ show tp ++ " to be a robust type (or if binding a var, it is used non-affinely)"
  show (PositiveType tp) = "Expected " ++ show tp ++ " to be a positive type (containing no arrow or ampersand types)"
  show NoCases = "Can't have case-of with no cases"
  show (MissingCases xs) = "Missing cases: " ++ intercalate ", " (show <$> xs)
  show (WrongNumCases exp act) = "Expected " ++ show exp ++ " cases, but got " ++ show act
  show (WrongNumArgs exp act) = "Expected " ++ show exp ++ " args, but got " ++ show act
  show (MultipleDefs x) = "Multiple definitions of " ++ x
  show ExternRecData = "Extern cannot use recursive datatypes"


{- ===== Constraints ===== -}
data Constraint = Unify Type Type | Robust Type | Positive Type

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
  substM (Positive tp) = pure Positive <*> substM tp

  freeVars (Unify tp1 tp2) = freeVars tp1 <> freeVars tp2
  freeVars (Robust tp) = freeVars tp
  freeVars (Positive tp) = freeVars tp

{- ===== CheckM Monad =====-}

type SolveVars = (Set Tag, Set TpVar)

-- Proxy for location, storing the current definition we're inside and the current expression
data Loc = Loc { curDef :: Maybe String, curExpr :: String }

instance Show Loc where
  show l = intercalate ", " ((case curDef l of Nothing -> []; Just v -> ["in the definition " ++ v]) ++ (if null (curExpr l) then [] else ["in the expression " ++ curExpr l]))

-- Reader part of the RWST monad for inference/checking
data CheckR = CheckR { checkEnv :: Ctxt, checkLoc :: Loc }

-- Temporarily modifies the env
modifyEnv :: (Ctxt -> Ctxt) -> CheckR -> CheckR
modifyEnv f cr = cr { checkEnv = f (checkEnv cr) }

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
occursCheck :: Substitutable a => TpVar -> a -> Bool
occursCheck x t = x `Map.member` freeTpVars (freeVars t)

-- Return the env
askEnv :: CheckM Ctxt
askEnv = checkEnv <$> ask

-- Return the current location
askLoc :: CheckM Loc
askLoc = checkLoc <$> ask

-- Modify the current location, storing a as the current def we are in
localCurDef :: Show a => a -> CheckM b -> CheckM b
localCurDef a = local (\ cr -> cr { checkLoc = (checkLoc cr) { curDef = Just (show a) } })

-- Modify the current location, storing a as the current expr we are in
localCurExpr :: Show a => a -> CheckM b -> CheckM b
localCurExpr a = local (\ cr -> cr { checkLoc = (checkLoc cr) { curExpr = show a } })

-- Add (x : tp) to env
inEnv :: TmVar -> Type -> CheckM a -> CheckM a
inEnv x tp = local $ modifyEnv (\ g -> ctxtAddLocal g x tp)

-- Checks for any duplicate definitions
anyDupDefs :: UsProgs -> CheckM ()
anyDupDefs (UsProgs ps etm) =
  either
    (err . MultipleDefs)
    (const okay)
    (foldlM hType (return Set.empty) ps >> foldlM hTerm (return Set.empty) ps)
  where
    addDef :: Show a => a -> Set String -> Either String (Set String)
    addDef x xs
      | show x `Set.member` xs = Left (show x)
      | otherwise = Right (Set.insert (show x) xs)
    
    hTerm :: Set String -> UsProg -> Either String (Set String)
    hTerm xs (UsProgDefine x atp tm) = addDef x xs
    hTerm xs (UsProgExtern x tp) = addDef x xs
    hTerm xs (UsProgData y ps cs) =
      foldlM (\ xs' (Ctor x tps) -> addDef x xs') (Right xs) cs
      
    hType :: Set String -> UsProg -> Either String (Set String)
    hType xs (UsProgData y ps cs) = addDef y xs
    hType xs _ = Right xs

-- Makes sure an extern's type has no recursive datatypes in it
guardExternRec :: Type -> CheckM ()
guardExternRec tp =
  askEnv >>= \ env ->
  guardM (not (isInfiniteType env tp)) ExternRecData

-- Defines a global function
defGlobal :: TmName -> [Tag] -> [Forall] -> Type -> CheckM a -> CheckM a
defGlobal x tgs ps tp = local $ modifyEnv ( \ g -> ctxtAddDefine g x tgs ps tp)

defExtern :: TmName -> Type -> CheckM a -> CheckM a
defExtern x tp = local $ modifyEnv ( \ g -> ctxtAddExtern g x tp)

-- Defines a datatype and its constructors
defData :: TpName -> [Tag] -> [TpVar] -> [Ctor] -> CheckM a -> CheckM a
defData y tgs ps cs = local $ modifyEnv (\ g -> ctxtAddData g y tgs ps cs)

-- Add (x1 : tp1), (x2 : tp2), ... to env
inEnvs :: [(TmVar, Type)] -> CheckM a -> CheckM a
inEnvs = flip $ foldr $ uncurry inEnv

-- Lookup a datatype
lookupDatatype :: TpName -> CheckM ([Tag], [TpVar], [Ctor])
lookupDatatype x =
  askEnv >>= \ g ->
  case Map.lookup x (tpNames g) of
    Just (CtData tgs ps cs) -> return (tgs, ps, cs)
    _ -> err (ScopeError (show x))

-- Lookup a term variable (local or global)
lookupTermVar :: TmVar -> CheckM (Either Type CtTerm)
lookupTermVar x =
  askEnv >>= \ g ->
  case Map.lookup x (tmVars g) of
    Just tp -> return (Left tp)
    Nothing -> case Map.lookup (tmVarToName x) (tmNames g) of
      Just d -> return (Right d)
      Nothing -> err (ScopeError (show x))

-- Lookup the datatype that cases split on
lookupCtorType :: [CaseUs] -> CheckM (TpName, [Tag], [TpVar], [Ctor])
lookupCtorType [] = err NoCases
lookupCtorType (CaseUs x _ _ : _) =
  fmap (Map.lookup x . tmNames) askEnv >>= \ d ->
  case d of
    Just (CtCtor _ _ ctp) -> case splitArrows ctp of
      (_, TpData y _ _) -> lookupDatatype y >>= \ (tgs, xs, cs) -> return (y, tgs, xs, cs)
      (_, etp) -> error "This shouldn't happen"
    _ -> err (CtorError x)

-- Returns the new type vars introduced by m
listenSolveVars :: CheckM a -> CheckM (a, SolveVars)
listenSolveVars m =
  get >>= \ vs ->
  m >>= \ a ->
  get >>= \ vs' ->
  return (a, diffSolveVars vs' vs)

diffSolveVars :: SolveVars -> SolveVars -> SolveVars
diffSolveVars (tags', tpVars') (tags, tpVars) =
  (Set.difference tags' tags, Set.difference tpVars' tpVars)

-- Adds a type variable to set of type variables to solve
addSolveTpVar :: TpVar -> CheckM ()
addSolveTpVar x = modify (\(tags, tpVars) -> (tags, Set.insert x tpVars))

-- Returns a fresh var (to solve) that doesn't collide with any being solved
freshTpVar :: CheckM TpVar
freshTpVar = state (\(tags, tpVars) -> let x = newVar (TpV "?0") (`Set.member` tpVars)
                                       in (x, (tags, Set.insert x tpVars)))

freshTagVar :: CheckM Tag
freshTagVar = state (\(tags, tpVars) -> let x = newVar (Tag "#0") (`Set.member` tags)
                                        in (x, (Set.insert x tags, tpVars)))

freshTp :: CheckM Type
freshTp = pure TpVar <*> freshTpVar

freshTag :: CheckM Tag
freshTag = freshTagVar

-- If NoTp, return a fresh type to solve; otherwise, check the type
annTp :: Type -> CheckM Type
annTp NoTp = freshTp
annTp tp = checkType tp

-- Ensures that a type is well-kinded (so no `List Bool Bool`, or use of undefined vars)
-- and adds tag variables to uses of datatypes, instantiating them to fresh variables
checkType :: Type -> CheckM Type
checkType (TpArr tp1 tp2) =
  pure TpArr <*> checkType tp1 <*> checkType tp2
checkType (TpData y [] as) =
  lookupDatatype y >>= \ (tgs, ps, _) ->
  mapM checkType as >>= \ as' ->
  mapM (const freshTag) tgs >>= \ tgs' ->
  guardM (length as == length ps) (WrongNumArgs (length ps) (length as)) >>
  pure (TpData y tgs' as')
checkType (TpData y tgs as) =
  error "checkType should never see a tag!"
checkType (TpProd am tps) =
  pure (TpProd am) <*> mapM checkType tps
checkType (TpVar y) =
  lookupDatatype (let TpV y' = y in TpN y') >>
  return (TpVar y)
checkType NoTp =
  error "checkType should never see a NoTp!"

-- Wrapper around infer', updating the current expr we are in (for better error messages)
infer :: UsTm -> CheckM Term
infer tm = localCurExpr tm (infer' tm)

-- Infers/checks a term, elaborating it from a user-term (UsTm) to a full Term
infer' :: UsTm -> CheckM Term

infer' (UsVar x) =
  -- Lookup the type of x
  lookupTermVar x >>= \ etp ->
  case etp of
    Left tp -> return (TmVarL x tp)
    Right (CtDefine tgs tis tp) -> h GlDefine tgs tis tp
    Right (CtExtern tp) -> h GlExtern [] [] tp
    Right (CtCtor tgs tis tp) -> h GlCtor tgs [Forall y BoundNone | y <- tis] tp
  where
    -- Any ∀-quantified type variables should be instantiated to fresh type variables
    h gv tgs tis tp =
     let ytis = [y | Forall y r <- tis] in
      -- pick new tags
      mapM (const freshTag) tgs >>= \ tgs' ->
      -- pick new type vars
      mapM (const freshTp) ytis >>= \ tis' ->
      -- ...that inherit any robustness constraints
      mapM (\ (Forall y bd, ytp) -> constrainIf (bd == BoundRobust) (Robust ytp)) (zip tis tis') >>
      -- substitute old tags/type vars for new ones
      let tp' = subst mempty{tags   = Map.fromList (pickyZip tgs tgs'),
                             tpVars = Map.fromList (pickyZip ytis tis')} tp in
        return (TmVarG gv (tmVarToName x) tgs' tis' [] tp')

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
      psub = mempty{tags   = Map.fromList (pickyZip tgs itgs),
                    tpVars = Map.fromList (pickyZip ps  ips)}
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
  constrain (Unify (TpData y itgs ips) (typeof tm')) >>
  -- itp = cases return type
  freshTp >>= \ itp ->
  -- infer cases
  mapM (uncurry inferCase) (pickyZip cs' ctors') >>= \ cs'' ->
  -- Constraints: for each case `| x ps -> tm`, itp = (typeof tm)
  mapM (\ (Case x ps tm) -> constrain (Unify itp (typeof tm))) cs'' >>
  return (TmCase tm' (y, itgs, ips) cs'' itp)

infer' (UsIf tm1 tm2 tm3) =
  infer tm1 >>= \ tm1' ->
  infer tm2 >>= \ tm2' ->
  infer tm3 >>= \ tm3' ->
  -- Constraint: Bool = (typeof tm1')
  constrain (Unify tpBool (typeof tm1')) >>
  -- Constraint: (typeof tm2') = (typeof tm3')
  constrain (Unify (typeof tm2') (typeof tm3')) >>
  -- Translate if-then-else to case-of
  return (TmCase tm1' (tpBoolName, [], []) [Case tmFalseName [] tm3', Case tmTrueName [] tm2'] (typeof tm2'))

infer' (UsTmBool b) =
  -- Translate True/False into a constructor var
  return (TmVarG GlCtor (if b then tmTrueName else tmFalseName) [] [] [] tpBool)

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

infer' (UsFactorDouble wt tm) =
  infer tm >>= \ tm' -> return (TmFactorDouble wt tm' (typeof tm'))

infer' (UsFactorNat wt tm) =
  infer tm >>= \ tm' -> return (TmFactorNat wt tm' (typeof tm'))

infer' (UsFactorRatio wt tm) =
  infer tm >>= \ tm' -> return (TmFactorRatio wt tm' (typeof tm'))

infer' (UsFail tp) =
  annTp tp >>= \ tp' ->
  return (TmAmb [] tp')

infer' (UsProd am tms) =
  mapM infer tms >>= \ tms' ->
  return (TmProd am [(tm, typeof tm) | tm <- tms'])

infer' (UsElimMultiplicative ptm xs tm) =
  infer ptm >>= \ ptm' ->
  -- Pick a fresh type var for each component
  mapM (\ x -> (,) x <$> freshTp) xs >>= \ ps ->
  -- For each (x : tp) in ps, if x is used more than affinely, constrain tp to be robust
  mapM (\ (x, tp) -> constrainIf (not $ isAff x tm) (Robust tp)) ps >>
  -- Constraint: (typeof ptm') = (ps1 * ps2 * ... * psn)
  constrain (Unify (typeof ptm') (TpProd Multiplicative (snds ps))) >>
  inEnvs ps (infer tm) >>= \ tm' ->
  return (TmElimMultiplicative ptm' ps tm' (typeof tm'))

infer' (UsElimAdditive ptm n i x tm) =
  infer ptm >>= \ ptm' ->
  -- Pick a fresh type var for each component
  replicateM n freshTp >>= \tps ->
  -- If x:tp is used more than affinely, constrain tp to be robust
  let xtp = tps !! i in
  constrainIf (not $ isAff x tm) (Robust xtp) >>
  -- Constraint: (typeof ptm') = (ps1 & ps2 & ... & psn)
  constrain (Unify (typeof ptm') (TpProd Additive tps)) >>
  inEnv x xtp (infer tm) >>= \ tm' ->
  return (TmElimAdditive ptm' n i (x,xtp) tm' (typeof tm'))

infer' (UsEqs tms) =
  mapM infer tms >>= \ tms' ->
  -- itp = type of all the tms
  freshTp >>= \ itp ->
  -- Constraint: for each tm in tms', itp = (typeof tm)
  mapM (constrain . Unify itp . typeof) tms' >>
  -- TODO: allow a weaker sense of type equality here, where datatype tags may be
  --       different; this would require ==-elimination to happen BETWEEN monomorph-
  --       ization of datatype parameters and datatype tags, so that you can compare
  --           List #i A == List #j B
  --       so long as you impose the constraint Unify A B (but no need to have #i = #j)
  -- Constraint: itp is positive
  constrain (Positive itp) >>
  return (TmEqs tms')

inferCase :: CaseUs -> Ctor -> CheckM Case
inferCase (CaseUs x xs tm) (Ctor x' ps) =
  -- Set the current expression to be the case `| x xs -> tm`
  localCurExpr (CaseUs x xs tm) $
  -- Guard against mismatched cases (probably gets caught earlier, in infer' (UsCase tm cs))
  guardM (x == x') (MissingCases [x']) >>
  -- Guard against wrong number of args
  guardM (length ps == length xs) (WrongNumArgs (length ps) (length xs)) >>
  let xps = pickyZip xs ps in
  -- For each (x : tp) in xps, if x is used more than affinely in tm, constrain tp to be robust
  mapM (\ (x, tp) -> constrainIf (not $ isAff x tm) (Robust tp)) xps >>
  inEnvs xps (infer tm) >>= \ tm' ->
  return (Case x xps tm')
