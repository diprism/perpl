-- Adapted from http://dev.stephendiehl.com/fun/006_hindley_milner.html

module TypeInf where
import Data.Char
import qualified Data.Map as Map
import Control.Monad.RWS.Lazy
import Control.Monad.Except
import Data.Functor.Identity
import Exprs
import Subst
--import Ctxt
import Free
import Util
import Name

-- Convention: expected type, then actual type
-- TODO: Enforce this convention
data TypeError =
    InfiniteType Var Type
  | UnificationError Type Type
  | ConflictingTypes Type Type
  | AffineError Var Term -- used more than affinely
  | ScopeError Var
  | RobustType Type
  | NoInference
  | NoCases

instance Show TypeError where
  show (InfiniteType x tp) = "Failed to construct infinite type: " ++ x ++ " := " ++ show tp
  show (ConflictingTypes tp1 tp2) = error "Conflicting types: " ++ show tp1 ++ " and " ++ show tp2
  show (AffineError x tm) = "'" ++ x ++ "' is not affine in " ++ show tm
  show (ScopeError x) = "'" ++ x ++ "' is not in scope"
  show (UnificationError tp1 tp2) = "Failed to unify " ++ show tp1 ++ " and " ++ show tp2
  show (RobustType tp) = "Expected " ++ show tp ++ " to be a robust type (or if binding a var, it is used non-affinely)"
  show NoInference = "Could not infer a type"
  show NoCases = "Can't have case-of with no cases"

--data Scheme = Forall [Var] Type
type Scheme = Type
--type TypeEnv = Map.Map Var Scheme
data Env = Env { typeEnv :: (Map.Map Var [Ctor]), termEnv :: (Map.Map Var Type) }

--extend :: TypeEnv -> (Var, Scheme) -> TypeEnv
--extend g (x, s) = Map.insert x s g

compose :: Subst -> Subst -> Subst
s1 `compose` s2 = Map.map (subst s1) s2 `Map.union` s1

{-
instance Substitutable Scheme where
  substM (Forall xs tp) =
    mapM freshen xs >>= \ xs' ->
    pure (Forall xs') <*> binds xs xs' (substM tp)

  freeVars (Forall xs tp) = foldr Map.delete (freeVars tp) xs
-}

data Constraint = Unify Type Type | Robust Type

getUnifications :: [(Constraint, Loc)] -> [(Type, Type, Loc)]
getUnifications [] = []
getUnifications ((Unify tp1 tp2, l) : cs) = (tp1, tp2, l) : getUnifications cs
getUnifications (_ : cs) = getUnifications cs

{-
data Constraints = Constraints { unifyCs :: [(Type, Type, Loc)], robustCs :: [(Type, Loc)], injectCs :: [(Type, Int, Type, Loc)] }
splitConstraints :: [(Constraint, Loc)] -> Constraints
splitConstraints =
  foldr (uncurry h) (Constraints { unifyCs = [], robustCs = [], injectCs = [] })
  where
    h (Unify tp1 tp2) l cs = cs { unifyCs = (tp1, tp2, l) : unifyCs cs }
    h (Robust tp) l cs = cs { robustCs = (tp, l) : robustCs cs }
    h (Inject tp1 o tp2) l cs = cs { injectCs = (tp1, o, tp2, l) : injectCs cs }
-}

instance Substitutable Constraint where
  substM (Unify tp1 tp2) = pure Unify <*> substM tp1 <*> substM tp2
  substM (Robust tp) = pure Robust <*> substM tp
--  substM (Inject ptp o tp) = pure Inject <*> substM ptp <*> pure o <*> substM tp

  freeVars (Unify tp1 tp2) = Map.union (freeVars tp1) (freeVars tp2)
  freeVars (Robust tp) = freeVars tp
--  freeVars (Inject ptp o tp) = Map.union (freeVars ptp) (freeVars tp)

type SolveVars = Map.Map Var Loc

data Loc = Loc { curDef :: String, curExpr :: String }

data CheckR = CheckR { checkEnv :: Env, checkLoc :: Loc }

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

localCurDef :: Show a => a -> CheckM b -> CheckM b
localCurDef a = local (\ cr -> cr { checkLoc = (checkLoc cr) { curDef = show a } })

localCurExpr :: Show a => a -> CheckM b -> CheckM b
localCurExpr a = local (\ cr -> cr { checkLoc = (checkLoc cr) { curExpr = show a } })

inEnv :: Var -> Type -> CheckM a -> CheckM a
inEnv x tp =
  local $ \ cr ->
  let env = checkEnv cr
      tme = termEnv env
      tme' = Map.insert x tp tme in
    cr { checkEnv = env { termEnv = tme' } }

inEnvs :: [(Var, Type)] -> CheckM a -> CheckM a
inEnvs = flip $ foldr $ uncurry inEnv

lookupType :: Var -> CheckM [Ctor]
lookupType x =
  ask >>= \ d ->
  maybe (err (ScopeError x)) return (Map.lookup x (typeEnv (checkEnv d)))

lookupTerm :: Var -> CheckM Type
lookupTerm x =
  ask >>= \ d ->
  maybe (err (ScopeError x)) return (Map.lookup x (termEnv (checkEnv d)))

lookupCtorType :: [CaseUs] -> CheckM (Var, [Ctor])
lookupCtorType [] = err NoCases
lookupCtorType (CaseUs x _ _ : _) =
  lookupTerm x >>= \ tp ->
  case tp of
    TpVar y -> (,) y <$> lookupType y
    _ -> err (ScopeError x) -- TODO: not a ctor?

boundVars :: CheckM (Map.Map Var ())
boundVars =
  ask >>= \ d ->
  get >>= \ s ->
  let env = checkEnv d
      tpe = typeEnv env
      tme = termEnv env in
  return (Map.unions [const () <$> tpe, const () <$> tme, const () <$> s])

fresh :: Var -> CheckM Var
fresh x = newVar x <$> boundVars

freshTpVar :: CheckM Var
freshTpVar =
  askLoc >>= \ l ->
  fresh "?" >>= \ x ->
  modify (Map.insert x l) >>
  return x

freshTp :: CheckM Type
freshTp = TpVar <$> freshTpVar

annTp :: Type -> CheckM Type
annTp NoTp = freshTp
annTp tp = checkType tp >> return tp

checkType :: Type -> CheckM ()
checkType (TpArr tp1 tp2) =
  checkType tp1 >> checkType tp2
checkType (TpVar y) =
  askEnv >>= \ env ->
  guardM (y `Map.member` typeEnv env) (ScopeError y)
checkType (TpProd am tps) =
  mapM_ checkType tps
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
  lookupTerm x >>= \ tp ->
  -- TODO: local or global?
  return (TmVarL x tp)

infer' (UsLam x xtp tm) =
  annTp xtp >>= \ xtp' ->
  inEnv x xtp' (infer tm) >>= \ tm' ->
  constrainIf (not $ isAff x tm) (Robust xtp') >>
  return (TmLam x xtp' tm' (typeof tm'))

-- TODO: if head is global var, add args
infer' (UsApp tm1 tm2) =
  infer tm1 >>: \ tm1' tp1 ->
  infer tm2 >>: \ tm2' tp2 ->
  freshTp >>= \ itp ->
  constrain (Unify tp1 (TpArr tp2 itp)) >>
  return (TmApp tm1' tm2' (typeof tm2') itp)

infer' (UsCase tm cs) =
  lookupCtorType cs >>= \ (y, ctors) ->
  guardM (length ctors == length cs) (error "TODO: wrong number of cases") >>
  -- TODO: make sure no duplicate cases (case x of True -> ... | True -> ...)
  let cs' = sortCases ctors cs in
  infer tm >>: \ tm' ytp ->
  constrain (Unify (TpVar y) ytp) >>
  freshTp >>= \ itp ->
  mapM inferCase cs' >>= \ cs'' ->
  mapM (\ (Case x ps tm) -> constrain (Unify itp (typeof tm))) cs'' >>
  return (TmCase tm' y cs'' itp)

infer' (UsIf tm1 tm2 tm3) =
  infer tm1 >>: \ tm1' tp1 ->
  infer tm2 >>: \ tm2' tp2 ->
  infer tm3 >>: \ tm3' tp3 ->
  constrain (Unify tp1 (TpVar "Bool")) >>
  constrain (Unify tp2 tp3) >>
  return (TmCase tm1' "Bool" [Case "False" [] tm3', Case "True" [] tm2'] tp2)

infer' (UsTmBool b) =
  return (TmVarG CtorVar (if b then "True" else "False") [] (TpVar "Bool"))

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

infer' (UsElimAmp tm (o, o')) =
  infer tm >>: \ tm' tp ->
  mapM (const freshTp) [1..o'] >>= \ itps ->
  constrain (Unify (TpProd Additive itps) tp) >>
  return (TmElimAmp tm' (o, o') (itps !! o))

infer' (UsProd am tms) =
  mapM infer tms >>= \ tms' ->
  return (TmProd am [(tm, typeof tm) | tm <- tms'])

infer' (UsElimProd ptm xs tm) =
  infer ptm >>: \ ptm' ptp ->
  mapM (\ x -> (,) x <$> freshTp) xs >>= \ ps ->
  mapM (\ (x, tp) -> constrainIf (not $ isAff x tm) (Robust tp)) ps >>
  inEnvs ps (infer tm) >>: \ tm' tp ->
  return (TmElimProd ptm' ps tm' tp)

infer' (UsEqs tms) =
  mapM infer tms >>= \ tms' ->
  freshTp >>= \ itp ->
  mapM (constrain . Unify itp . typeof) tms' >>
  constrain (Robust itp) >>
  return (TmEqs tms')

inferCase :: CaseUs -> CheckM Case
inferCase (CaseUs x xs tm) = error "TODO"


bindTp :: Var -> Type -> Either TypeError Subst
bindTp x tp
  | tp == TpVar x = Right Map.empty
  | occursCheck x tp = Left (InfiniteType x tp)
  | otherwise = Right (Map.singleton x (SubTp tp))

unify :: Type -> Type -> Either TypeError Subst
unify (TpVar y) tp = bindTp y tp
unify tp (TpVar y) = bindTp y tp
unify (TpArr l1 r1) (TpArr l2 r2) =
  unify l1 l2 >>= \ sl ->
  unify (subst sl r1) (subst sl r2) >>= \ sr ->
  return (sr `compose` sl)
unify (TpProd am1 tps1) (TpProd am2 tps2)
  | (am1 /= am2) || (length tps1 /= length tps2) =
      Left (UnificationError (TpProd am1 tps1) (TpProd am2 tps2))
  | otherwise =
      unifyAll' (zip tps1 tps2)
unify NoTp tp = error "unify should not receive a NoTp"
unify tp NoTp = error "unify should not receive a NoTp"
unify tp1 tp2 = Left (UnificationError tp1 tp2)

-- TODO: Need a unify for injections, e.g. if you have
-- \ x. foo <x.1, x.2, x.3>
-- where foo : (A & B & C) -> D    for some A, B, C, D
-- Will need to consider when to apply these constraints--
-- should they be interspersed with regular unifications?
-- Or after? Probably after, I think...

unifyAll' :: [(Type, Type)] -> Either TypeError Subst
unifyAll' tps = mapLeft fst $ unifyAll [(tp1, tp2, Loc { curDef = "", curExpr = ""}) | (tp1, tp2) <- tps]

unifyAll :: [(Type, Type, Loc)] -> Either (TypeError, Loc) Subst
unifyAll =
  foldr
    (\ (tp1, tp2, l) s ->
        s >>= \ s ->
        mapLeft (\ e -> (e, l)) (unify (subst s tp1) (subst s tp2)) >>= \ s' ->
        return (s' `compose` s))
    (Right Map.empty)

isRobust :: Env -> Type -> Bool
isRobust g = h [] where
  h visited (TpVar y) = (y `elem` visited) || maybe False (any $ \ (Ctor _ tps) -> any (h (y : visited)) tps) (Map.lookup y (typeEnv g))
  h visited (TpArr _ _) = True
  h visited (TpProd am tps) = am == Additive || any (h visited) tps
  h visited NoTp = False

solvedWell :: Env -> Subst -> [(Constraint, Loc)] -> Either (TypeError, Loc) ()
solvedWell e s cs = sequence [ h (subst s c) l | (c, l) <- cs ] >> okay where
  h (Unify tp1 tp2) l
    | tp1 /= tp2 = Left (ConflictingTypes tp1 tp2, l)
    | otherwise = okay
  h (Robust tp) l
    | not (isRobust e tp) = Left (RobustType tp, l)
    | otherwise = okay
--  h (Inject (TpProd am tps) o tp) l
--    | am == Multiplicative = Left (error "TODO: new error? Or reuse?", l)
--    | o >= length tps = Left (error "TODO: (another) new error? Or reuse?", l)
--    | tps !! o /= tp = Left (ConflictingTypes (tps !! 0) tp, l)
--    | otherwise = okay
--  h (Inject ptp o tp) l = Left (error "TODO: new error", l)

--isSolved :: Var -> Loc -> Subst -> Either (TypeError, Loc) ()
--isSolved x l s = maybe () () (Map.lookup 

allSolved :: SolveVars -> Subst -> Type -> Either (TypeError, Loc) [Var]
--allSolved vs s = foldr (\ (x, l) e -> Left (NoInference, l)) okay (Map.toList (Map.difference vs s))
allSolved vs s rtp =
  let unsolved = Map.difference vs s
      fvs = freeVars rtp
      internalUnsolved = Map.difference unsolved fvs
  in
    if null internalUnsolved
    then Left (NoInference, (snd $ head $ Map.toList internalUnsolved))
    else Right (Map.keys fvs)

solve :: Env -> SolveVars -> [(Constraint, Loc)] -> Type -> Either (TypeError, Loc) Subst
solve g vs cs rtp =
    unifyAll (getUnifications cs) >>= \ s ->
    solvedWell g s cs >>
    allSolved vs s rtp >>
    return s
