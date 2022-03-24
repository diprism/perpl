-- Adapted from http://dev.stephendiehl.com/fun/006_hindley_milner.html

module TypeInf where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.RWS.Lazy
import Control.Monad.Except
import Exprs
import Subst
import Free
import Util
import Name
import Show()
import Tarjan

data Scope = ScopeLocal | ScopeGlobal | ScopeCtor
  deriving Eq

-- Convention: expected type, then actual type
-- TODO: Enforce this convention
data TypeError =
    InfiniteType Var Type
  | UnificationError Type Type
  | ConflictingTypes Type Type
  | AffineError Var Term -- used more than affinely
  | ScopeError Var
  | RobustType Type
--  | NoInference
  | NoCases
  | ExpNonUnderscoreVar
  | ExpOneNonUnderscoreVar
  | MissingCases [Var]
  | WrongNumCases Int Int
  | WrongNumArgs Int Int

instance Show TypeError where
  show (InfiniteType x tp) = "Failed to construct infinite type: " ++ x ++ " := " ++ show tp
  show (ConflictingTypes tp1 tp2) = "Conflicting types: " ++ show tp1 ++ " and " ++ show tp2
  show (AffineError x tm) = "'" ++ x ++ "' is not affine in " ++ show tm
  show (ScopeError x) = "'" ++ x ++ "' is not in scope"
  show (UnificationError tp1 tp2) = "Failed to unify " ++ show tp1 ++ " and " ++ show tp2
  show (RobustType tp) = "Expected " ++ show tp ++ " to be a robust type (or if binding a var, it is used non-affinely)"
--  show NoInference = "Could not infer a type"
  show NoCases = "Can't have case-of with no cases"
  show ExpNonUnderscoreVar = "Expected non-underscore variable here"
  show ExpOneNonUnderscoreVar = "Expected exactly one non-underscore variable"
  show (MissingCases xs) = "Missing cases: " ++ delimitWith ", " xs
  show (WrongNumCases exp act) = "Expected " ++ show exp ++ " cases, but got " ++ show act
  show (WrongNumArgs exp act) = "Expected " ++ show exp ++ " args, but got " ++ show act

data Env = Env { typeEnv :: Map Var [Ctor],
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

type SolveVars = Map Var Loc

data Loc = Loc { curDef :: String, curExpr :: String }

instance Show Loc where
  show l = delimitWith ", " ((if null (curDef l) then [] else ["in the definition " ++ curDef l]) ++ (if null (curExpr l) then [] else ["in the expression " ++ curExpr l]))

data CheckR = CheckR { checkEnv :: Env, checkLoc :: Loc }

modifyEnv :: (Env -> Env) -> CheckR -> CheckR
modifyEnv f cr = cr { checkEnv = f (checkEnv cr) }

typeEnvInsert :: Var -> [Ctor] -> CheckR -> CheckR
typeEnvInsert y cs = modifyEnv $ \ e -> e { typeEnv = Map.insert y cs (typeEnv e) }

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

defTerm :: Var -> GlobalVar -> Scheme -> CheckM a -> CheckM a
defTerm x g tp = local $ globalEnvInsert x g tp

defType :: Var -> [Ctor] -> CheckM a -> CheckM a
defType y cs = local $ typeEnvInsert y cs

defData :: Var -> [Ctor] -> CheckM a -> CheckM a
defData y cs m =
  foldr
    (\ (Ctor x tps) -> defTerm x CtorVar (Forall [] (joinArrows tps (TpVar y))))
    (defType y cs m) cs

inEnvs :: [(Var, Type)] -> CheckM a -> CheckM a
inEnvs = flip $ foldr $ uncurry inEnv

lookupType :: Var -> CheckM [Ctor]
lookupType x =
  askEnv >>= \ g ->
  maybe (err (ScopeError x)) return (Map.lookup x (typeEnv g))

lookupTerm :: Var -> CheckM (Either Type (GlobalVar, Scheme))
lookupTerm x =
  askEnv >>= \ g ->
  maybe (err (ScopeError x)) return ((Left <$> Map.lookup x (localEnv g)) |?| (Right <$> Map.lookup x (globalEnv g)))

lookupCtorType :: [CaseUs] -> CheckM (Var, [Ctor])
lookupCtorType [] = err NoCases
lookupCtorType (CaseUs x _ _ : _) =
  lookupTerm x >>= \ etp ->
  case etp of
    Right (CtorVar, Forall [] (TpVar y)) -> (,) y <$> lookupType y
    _ -> err (ScopeError x) -- TODO: not a ctor?

boundVars :: CheckM (Map Var ())
boundVars =
  ask >>= \ d ->
  get >>= \ s ->
  let env = checkEnv d
      tpe = typeEnv env
      lce = localEnv env
      gbe = globalEnv env in
  return (Map.unions [const () <$> tpe, const () <$> lce, const () <$> gbe, const () <$> s])

fresh :: Var -> CheckM Var
fresh x = newVar x <$> boundVars

freshTpVar :: CheckM Var
freshTpVar =
  askLoc >>= \ l ->
  fresh "?0" >>= \ x ->
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
  guardM (x /= "_") ExpNonUnderscoreVar >>
  lookupTerm x >>= \ etp ->
  case etp of
    Left tp -> return (TmVarL x tp)
    Right (gv, Forall tis tp) ->
      mapM (const freshTp) tis >>= \ tis' ->
      let tp' = subst (Map.fromList (zip tis (SubTp <$> tis'))) tp in
      return (TmVarG gv x tis' [] tp')

infer' (UsLam x xtp tm) =
  annTp xtp >>= \ xtp' ->
  inEnv x xtp' (infer tm) >>= \ tm' ->
  constrainIf (not $ isAff x tm) (Robust xtp') >>
  return (TmLam x xtp' tm' (typeof tm'))

infer' (UsApp tm1 tm2) =
  infer tm1 >>: \ tm1' tp1 ->
  infer tm2 >>: \ tm2' tp2 ->
  freshTp >>= \ itp ->
  constrain (Unify tp1 (TpArr tp2 itp)) >>
  return (TmApp tm1' tm2' (typeof tm2') itp)

infer' (UsCase tm cs) =
  lookupCtorType cs >>= \ (y, ctors) ->
  let cs' = sortCases ctors cs
      cs_map = Map.fromList [(x, ()) | (CaseUs x _ _) <- cs]
      ctors_map = Map.fromList [(y, ()) | (Ctor y _) <- ctors]
      missingCases = Map.difference ctors_map cs_map in
  guardM (null missingCases) (MissingCases (Map.keys missingCases)) >>
  guardM (length ctors == length cs) (WrongNumCases (length ctors) (length cs)) >>
  infer tm >>: \ tm' ytp ->
  constrain (Unify (TpVar y) ytp) >>
  freshTp >>= \ itp ->
  mapM (uncurry inferCase) (zip cs' ctors) >>= \ cs'' ->
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
  return (TmVarG CtorVar (if b then "True" else "False") [] [] (TpVar "Bool"))

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

-- Returns all type inst vars in an expression
--unboundVars :: Substitutable a => a -> CheckM [Var]
--unboundVars a = pure (Map.keys . Map.intersection (freeVars a)) <*> get

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
  h visited (TpVar y) = (y `elem` visited) || maybe True (all $ \ (Ctor _ tps) -> all (h (y : visited)) tps) (Map.lookup y (typeEnv g))
  h visited (TpArr _ _) = False
  h visited (TpProd am tps) = am == Additive || any (h visited) tps
  h visited NoTp = True

solvedWell :: Env -> Subst -> [(Constraint, Loc)] -> Either (TypeError, Loc) ()
solvedWell e s cs = sequence [ h (subst s c) l | (c, l) <- cs ] >> okay where
  h (Unify tp1 tp2) l
    | tp1 /= tp2 = Left (ConflictingTypes tp1 tp2, l)
    | otherwise = okay
  h (Robust tp) l
    | not (isRobust e tp) = Left (RobustType tp, l)
    | otherwise = okay

solveInternal :: SolveVars -> Subst -> Type -> (Subst, [Var])
solveInternal vs s rtp =
  let unsolved = Map.difference vs s
      fvs = freeVars rtp
      internalUnsolved = Map.difference unsolved fvs
      s' = foldr (\ ix -> Map.insert ix (SubTp tpUnit)) Map.empty (Map.keys internalUnsolved)
      s'' = s' `compose` s
  in
    (s'', Map.keys (Map.intersection unsolved fvs))

solve :: Env -> SolveVars -> Type -> [(Constraint, Loc)] -> Either (TypeError, Loc) (Subst, [Var])
solve g vs rtp cs =
  unifyAll (getUnifications cs) >>= \ s ->
  let (s', xs) = solveInternal vs s rtp in
  solvedWell g s' cs >>
  return (s', xs)

--solveM :: Substitutable a => CheckM (a, Type) -> CheckM (a, Scheme)
solveM :: CheckM (Term, Type) -> CheckM (Term, Scheme)
solveM m =
  get >>= \ vs ->
  listen m >>= \ ((a, tp), cs) ->
  pure solve <*> askEnv <*> (fmap (\ vs' -> Map.difference vs' vs) get) <*> pure tp <*> pure cs >>=
  either throwError (\ (s, xs) -> return (subst s a, Forall xs (subst s tp)))

solvesM :: [(Var, Type)] -> CheckM [(Var, Term, Type)] -> CheckM [(Var, Term, Scheme)]
solvesM itps ms =
  get >>= \ vs ->
  listen ms >>= \ (atps, cs) ->
  let (fs, as, tps) = unzip3 atps in
  pure solve <*> askEnv <*> (fmap (\ vs' -> Map.difference vs' vs) get) <*> pure (TpProd Multiplicative tps) <*> pure cs >>=
  either throwError (\ (s, xs) ->
                        let stps = map (\ tp ->
                                          let tp' = subst s tp
                                              xs' = Map.keys (Map.intersection (Map.fromList (map (\ x -> (x, ())) xs)) (freeVars tp')) in
                                            Forall xs' tp') tps
                            s' = foldr (\ (fx, Forall xs' tp') -> Map.insert fx (SubTm (TmVarG DefVar fx (map TpVar xs') [] tp'))) s (zip fs stps) in
                          return (zip3 fs (subst s as) stps))


getDeps :: UsProgs -> Map Var (Set Var)
getDeps (UsProgs ps end) = clean (foldr h mempty ps) where
  -- Removes ctors and externs from each set in the map
  clean :: Map Var (Set Var) -> Map Var (Set Var)
  clean m = let s = Set.fromList (Map.keys m) in fmap (Set.intersection s) m
  
  h :: UsProg -> Map Var (Set Var) -> Map Var (Set Var)
  h (UsProgFun x mtp tm) deps = Map.insert x (Set.fromList (Map.keys (freeVars tm))) deps
  h (UsProgExtern x tp) deps = deps -- Map.insert x mempty deps
  h (UsProgData y cs) deps = deps -- foldr (\ (Ctor x tps) -> Map.insert x mempty) deps cs

splitProgsH :: UsProg -> ([(Var, Type, UsTm)], [(Var, Type)], [(Var, [Ctor])])
splitProgsH (UsProgFun x mtp tm) = ([(x, mtp, tm)], [], [])
splitProgsH (UsProgExtern x tp) = ([], [(x, tp)], [])
splitProgsH (UsProgData y cs) = ([], [], [(y, cs)])

splitProgs :: UsProgs -> ([(Var, Type, UsTm)], [(Var, Type)], [(Var, [Ctor])], UsTm)
splitProgs (UsProgs ps end) =
  let (fs, es, ds) = foldr (\ p (fs, es, ds) ->
                               let (fs', es', ds') = splitProgsH p in
                                 (fs' ++ fs, es' ++ es, ds' ++ ds))
                           ([], [], []) ps in
    (fs, es, ds, end)

mapMl :: Monad m => (a -> m b) -> [a] -> m [b]
mapMl f = fmap reverse . mapM f . reverse

inferFuns :: [(Var, Type, UsTm)] -> CheckM SProgs -> CheckM SProgs
inferFuns fs m =
  mapM (\ (x, mtp, tm) -> annTp mtp) fs >>= \ itps ->
  let ftps = [(x, itp) | ((x, _, _), itp) <- zip fs itps]
      defs = \ m -> foldl (\ m (x, itp) -> inEnv x itp m) m ftps in
--    error (show ftps)
    defs
    (solvesM ftps
      (mapM (\ ((x, _, tm), tp) ->
               localCurDef x $
               infer tm >>: \ tm' tp' ->
               constrain (Unify tp tp') >>
               return (x, tm', tp')) (zip fs itps))) >>= \ xtmstps ->
    foldr (\ (x, tm, stp) -> defTerm x DefVar stp) m xtmstps >>= \ (SProgs ps end) ->
    let ps' = map (\ (x, tm, stp) -> SProgFun x stp tm) xtmstps in
    return (SProgs (ps' ++ ps) end)

inferData :: (Var, [Ctor]) -> CheckM SProgs -> CheckM SProgs
inferData (y, cs) m =
  -- We will check each of the ctor type args later,
  -- after every datatype has been added to the environment
  defData y cs m >>= \ (SProgs ps end) ->
  return (SProgs (SProgData y cs : ps) end)

inferExtern :: (Var, Type) -> CheckM SProgs -> CheckM SProgs
inferExtern (x, tp) m =
  localCurDef x (checkType tp) >>
  defTerm x DefVar (Forall [] tp) m >>= \ (SProgs ps end) ->
  return (SProgs (SProgExtern x [] tp : ps) end)

inferProgs :: UsProgs -> CheckM SProgs
inferProgs ps =
  let m = getDeps ps
      (fs, es, ds, end) = splitProgs ps
      mfs = Map.fromList [(x, (tp, tm)) | (x, tp, tm) <- fs]
      -- sccs is a list of strongly connected functions.
      -- you can check it in order, by checking together
      -- all the functions in each strongly connected set
      sccs = tarjan m
      sccs' = [[let (tp, tm) = mfs Map.! x in (x, tp, tm) | x <- scc] | scc <- sccs]
  in
    -- TODO: maybe sort progs back into original order?
    
    -- Add datatype defs to environment
    foldl (flip inferData)
      -- Check the type args in each datatype
      (mapM (\ (y, cs) -> mapM (\ (Ctor x tps) -> mapM checkType tps) cs) ds >>
      -- Then check externs
       foldl (flip inferExtern)
       -- Then check functions
         (foldl (flip inferFuns)
         -- Then check end term
            (solveM (infer end >>: curry return) >>= \ (end', Forall tpms tp) ->
             -- guardM (null tpms) (error "TODO: end term should not have type polymorphism") >>
             return (SProgs [] end')) sccs') es) ds


inferFile :: UsProgs -> Either String SProgs
inferFile ps =
  either (\ (e, loc) -> Left (show e ++ ", " ++ show loc)) (\ (a, s, w) -> Right a)
    (runExcept (runRWST (inferProgs (progBool ps))
                        (CheckR (Env mempty mempty mempty) (Loc "" "")) mempty))

{-
declareProgs :: UsProgs -> CheckM a -> CheckM a
declareProgs (UsProgExec tm) m = m
declareProgs (UsProgFun x NoTp tm ps) m =
  localCurDef x freshTpVar >>= \ itp ->
  defTerm x DefVar (Forall [itp] (TpVar itp)) (declareProgs ps m)
declareProgs (UsProgFun x tp tm ps) m =
  defTerm x DefVar (Forall [] tp) (declareProgs ps m)
declareProgs (UsProgExtern x tp ps) m =
  defTerm x DefVar (Forall [] tp) (declareProgs ps m)
declareProgs (UsProgData y cs ps) m =
  defData y cs (declareProgs ps m)

inferProgs :: UsProgs -> CheckM SProgs
inferProgs (UsProgExec tm) =
  solveM (infer tm >>: curry return) >>= \ (tm', tp) ->
  return (SProgs [] tm')
inferProgs (UsProgFun x NoTp tm ps) =
  localCurDef x (solveM (infer tm >>: curry return)) >>= \ (tm', stp) ->
  inferProgs ps >>= \ (SProgs ps end) ->
  let p = SProgFun x stp tm' in
  return (SProgs (p : ps) end)
inferProgs (UsProgFun x tp tm ps) =
  localCurDef x
    (checkType tp >>
     solveM (infer tm >>: \ tm' tp' ->
             constrain (Unify tp tp') >>
             return (tm', tp'))) >>= \ (tm', stp) ->
  inferProgs ps >>= \ (SProgs ps end) ->
  let p = SProgFun x stp tm' in
  return (SProgs (p : ps) end)
inferProgs (UsProgExtern x tp ps) =
  inferProgs ps >>= \ (SProgs ps end) ->
  return (SProgs (SProgExtern x [] tp : ps) end)
inferProgs (UsProgData y cs ps) =
  mapM (\ (Ctor x tps) -> mapM checkType tps) cs >>
  inferProgs ps >>= \ (SProgs ps end) ->
  return (SProgs (SProgData y cs : ps) end)

-- TODO: replace gv tis of just one thing with the actual type inst vars as determined later
inferFile :: UsProgs -> Either String SProgs
inferFile ps =
  either (\ (e, loc) -> Left (show e ++ ", " ++ show loc)) (\ (a, s, w) -> Right a)
    (runExcept (runRWST (declareProgs (progBool ps) (inferProgs ps)) (CheckR (Env mempty mempty mempty) (Loc "" "")) mempty))
-}
