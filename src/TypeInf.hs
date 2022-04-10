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
import SCC

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
  fresh "?0" >>= \ x ->
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
  return (TmCase tm' (y, ips) cs'' itp)

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

-- Returns all type inst vars in an expression
--unboundVars :: Substitutable a => a -> CheckM [Var]
--unboundVars a = pure (Map.keys . Map.intersection (freeVars a)) <*> get

bindTp :: Var -> Type -> Either TypeError Subst
bindTp x tp
  | tp == TpVar x [] = Right Map.empty
  | occursCheck x tp = Left (InfiniteType x tp)
  | otherwise = Right (Map.singleton x (SubTp tp))

unify :: Type -> Type -> Either TypeError Subst
unify (TpVar y@('?' : _) []) tp = bindTp y tp -- Only substitute type inst vars
unify tp (TpVar y@('?' : _) []) = bindTp y tp -- Same ^
unify tp1@(TpVar y1 as1) tp2@(TpVar y2 as2)
  | y1 == y2 && length as1 == length as2 =
      unifyAll' (zip as1 as2)
    --mapM (uncurry unify) (zip as1 as2) >>= \ ss ->
    --  Right (foldr compose mempty ss)
  | otherwise = Left (UnificationError tp1 tp2)
--unify (TpVar y) tp = bindTp y tp
--unify tp (TpVar y) = bindTp y tp
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
unify tp1 tp2
  | tp1 == tp2 = Right Map.empty
  | otherwise  = Left (UnificationError tp1 tp2)

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

solvedWell :: Env -> Subst -> [(Constraint, Loc)] -> Either (TypeError, Loc) ()
solvedWell e s cs = sequence [ h (subst s c) l | (c, l) <- cs ] >> okay where
  robust' = robust $ \ y -> fmap (\ (_, _, cs) -> cs) (Map.lookup y (typeEnv e))

  h (Unify tp1 tp2) l
    | tp1 /= tp2 = Left (ConflictingTypes tp1 tp2, l)
    | otherwise = okay
  h (Robust tp) l
    | not (robust' tp) = Left (RobustType tp, l)
    | otherwise = okay


solveInternal :: SolveVars -> Subst -> Type -> (Subst, [Var], [Var])
solveInternal vs s rtp =
  let unsolved = Map.difference vs s
      fvs = freeVars (subst s rtp)
      (tags, internalUnsolved) = Map.partition id (Map.difference unsolved fvs)
      s' = fmap (\ tg -> SubTp tpUnit) internalUnsolved -- foldr (\ (ix, tg) -> Map.insert ix (SubTp tpUnit)) Map.empty (Map.toList internalUnsolved)
      s'' = s' `compose` s
  in
--    if null internalUnsolved then
    (s'', Map.keys (Map.intersection unsolved fvs), Map.keys tags)
--    else error ("internalUnsolved: " ++ show internalUnsolved ++ ", vs: " ++ show vs ++ ", s: " ++ show s ++ ", rtp: " ++ show (subst s rtp) ++ ", rtp2: " ++ show (subst s'' rtp))

solve :: Env -> SolveVars -> Type -> [(Constraint, Loc)] -> Either (TypeError, Loc) (Subst, [Var], [Var])
solve g vs rtp cs =
  unifyAll (getUnifications cs) >>= \ s ->
  let (s', xs, tgs) = solveInternal vs s rtp
  in
  solvedWell g s' cs >>
  return (s', xs, tgs)

solveM :: CheckM (Term, Type) -> CheckM (Term, Type, [Var]) -- [Var] is list of tags
solveM m =
  listenSolveVars (listen m) >>= \ (((a, tp), cs), vs) ->
  pure solve <*> askEnv <*> pure vs <*> pure {-tp-} NoTp <*> pure cs >>=
  either throwError (\ (s, [], tgs) -> return (subst s a, subst s tp, tgs))

solvesM :: [(Var, Type)] -> CheckM [(Var, Term, Type)] -> CheckM [(Var, Term, Scheme)]
solvesM itps ms =
  listenSolveVars (listen ms) >>= \ ((atps, cs), vs) ->
  let (fs, as, tps) = unzip3 atps in
  pure solve <*> askEnv <*> pure vs <*> pure (TpProd Multiplicative tps) <*> pure cs >>=
  either
    throwError
    (\ (s, xs, tgs) ->
        let stps = map (\ tp ->
                          let tp' = subst s tp
                              xsmap = Map.fromList (map (\ x -> (x, ())) xs)
                              xs' = Map.keys (Map.intersection xsmap (freeVars tp'))
                          in
                            Forall tgs xs' tp') tps

            s' = foldr (\ (fx, Forall tgs' xs' tp') ->
                          Map.insert fx
                            (SubTm (TmVarG DefVar fx
                                    (map (\ x -> TpVar x []) (tgs' ++ xs')) [] tp')))
                       s (zip fs stps)
        in
          return (zip3 fs (subst s' as) stps))


-- Returns (function dependencies, datatype dependencies)
getDeps :: UsProgs -> (Map Var (Set Var), Map Var (Set Var))
getDeps (UsProgs ps end) =
  let (fdeps, ddeps) = foldr h mempty ps in
    (clean fdeps, clean ddeps)
  where
    -- Removes ctors, externs, type parameters from each set in the map
    clean :: Map Var (Set Var) -> Map Var (Set Var)
    clean m = let s = Set.fromList (Map.keys m) in fmap (Set.intersection s) m
    
    h :: UsProg -> (Map Var (Set Var), Map Var (Set Var)) -> (Map Var (Set Var), Map Var (Set Var))
    h (UsProgFun x mtp tm) (fdeps, ddeps) =
      (Map.insert x (Set.fromList (Map.keys (freeVars tm))) fdeps, ddeps)
    h (UsProgExtern x tp) deps = deps
    h (UsProgData y ps cs) (fdeps, ddeps) =
      (fdeps, Map.insert y (Set.fromList (Map.keys (freeVars cs))) ddeps)

splitProgsH :: UsProg -> ([(Var, Type, UsTm)], [(Var, Type)], [(Var, [Var], [Ctor])])
splitProgsH (UsProgFun x mtp tm) = ([(x, mtp, tm)], [], [])
splitProgsH (UsProgExtern x tp) = ([], [(x, tp)], [])
splitProgsH (UsProgData y ps cs) = ([], [], [(y, ps, cs)])

splitProgs :: UsProgs -> ([(Var, Type, UsTm)], [(Var, Type)], [(Var, [Var], [Ctor])], UsTm)
splitProgs (UsProgs ps end) =
  let (fs, es, ds) = foldr (\ p (fs, es, ds) ->
                               let (fs', es', ds') = splitProgsH p in
                                 (fs' ++ fs, es' ++ es, ds' ++ ds))
                           ([], [], []) ps in
    (fs, es, ds, end)

inferFuns :: [(Var, Type, UsTm)] -> CheckM SProgs -> CheckM SProgs
inferFuns fs m =
  mapM (\ (x, mtp, tm) -> annTp mtp) fs >>= \ itps ->
  let ftps = [(x, itp) | ((x, _, _), itp) <- zip fs itps] in
    inEnvs ftps
    (solvesM ftps
      (mapM (\ ((x, _, tm), tp) ->
               localCurDef x $
               infer tm >>: \ tm' tp' ->
               constrain (Unify tp tp') >>
               return (x, tm', tp')) (zip fs itps))) >>= \ xtmstps ->
    foldr (\ (x, tm, stp) -> defTerm x DefVar stp) m xtmstps >>= \ (SProgs ps end) ->
    let ps' = map (\ (x, tm, stp) -> SProgFun x stp tm) xtmstps in
    return (SProgs (ps' ++ ps) end)

{-inferData :: [Var] -> (Var, [Var], [Ctor]) -> CheckM SProgs -> CheckM SProgs
inferData recs (y, xs, cs) m =
  -- We will check each of the ctor type args later,
  -- after every datatype has been added to the environment
  (if y `elem` recs then (freshTagVar >>= \ x -> return [x]) else (return [])) >>= \ tgs ->
  defData y tgs xs cs m >>= \ (SProgs ps end) ->
  return (SProgs (SProgData y tgs xs cs : ps) end)
-}

inferData :: [[(Var, [Var], [Ctor])]] -> CheckM SProgs -> CheckM SProgs
inferData dsccs cont = foldr h cont dsccs
  where
    recs :: [Var]
    recs = getRecTypes' (concat [[(y, [], ps, cs) | (y, ps, cs) <- dscc] | dscc <- dsccs])
    
    sccIsRec :: [(Var, [Var], [Ctor])] -> Bool
    sccIsRec [(y, ps, cs)] = y `elem` recs
    sccIsRec _ = True -- Mutually-recursive datatypes are recursive
    
    checkCtor :: Ctor -> CheckM Ctor
    checkCtor (Ctor x tps) =
      pure (Ctor x) <*> mapM checkType tps

    addDefs :: [(Var, [Var], [Var], [Ctor])] -> CheckM SProgs -> CheckM SProgs
    addDefs [] cont = cont
    addDefs ((y, tgs, ps, cs) : ds) cont =
      defData y tgs ps cs (addDefs ds cont) >>= \ (SProgs sps etm) ->
      return (SProgs (SProgData y tgs ps cs : sps) etm)

    --defDatas m = foldr (\ ) m ds
    h :: [(Var, [Var], [Ctor])] -> CheckM SProgs -> CheckM SProgs
    h dscc cont =
      hPerhapsRec dscc >>= \ dscc' ->
      addDefs dscc' cont

    hPerhapsRec :: [(Var, [Var], [Ctor])] -> CheckM [(Var, [Var], [Var], [Ctor])]
    hPerhapsRec dscc = if sccIsRec dscc then hRec dscc else hNonRec dscc

    substTagsCtors :: Map Var [Var] -> [Ctor] -> [Ctor]
    substTagsCtors s = map $ \ (Ctor x tps) -> Ctor x (map (substTags s) tps)

    hRec :: [(Var, [Var], [Ctor])] -> CheckM [(Var, [Var], [Var], [Ctor])]
    hRec dscc =
      freshTagVar >>= \ itg ->
      listenSolveVars
        (foldl
           (\ m (y, ps, cs) -> defType y [] ps cs m)
           (mapM (\ (y, ps, cs) ->
                    pure ((,,) y ps) <*> mapM (\ (Ctor x tps) ->
                                                 pure (Ctor x) <*> mapM checkType tps)
                                              cs) dscc)
           dscc)
        >>= \ (dscc', vs) ->
      let tgs = itg : Map.keys (Map.filter id vs)
          s = Map.fromList [(y, tgs) | (y, ps, cs) <- dscc']
      in
        return [(y, tgs, ps, substTagsCtors s cs) | (y, ps, cs) <- dscc']
    
    hNonRec :: [(Var, [Var], [Ctor])] -> CheckM [(Var, [Var], [Var], [Ctor])]
    hNonRec [(y, ps, cs)] =
      listenSolveVars (defParams ps (mapM checkCtor cs)) >>= \ (cs', vs) ->
      let tgs = Map.keys (Map.filter id vs) in
        return [(y, tgs, ps, cs')]
    hNonRec _ = error "this shouldn't happen"
    

inferExtern :: (Var, Type) -> CheckM SProgs -> CheckM SProgs
inferExtern (x, tp) m =
  localCurDef x (checkType tp) >> -- tp can't have rec datatypes, this returns same tp
  defTerm x DefVar (Forall [] [] tp) m >>= \ (SProgs ps end) ->
  return (SProgs (SProgExtern x [] tp : ps) end)

inferProgs :: UsProgs -> CheckM SProgs
inferProgs ps =
  let (fdeps, ddeps) = getDeps ps
      (fs, es, ds, end) = splitProgs ps
      mfs = Map.fromList [(x, (tp, tm)) | (x, tp, tm) <- fs]
      mds = Map.fromList [(x, (ps, cs)) | (x, ps, cs) <- ds]
      -- sccs is a list of strongly connected functions.
      -- you can check it in order, by checking together
      -- all the functions in each strongly connected set
      funSCCs   = scc fdeps
      dataSCCs  = scc ddeps
      funSCCs'  = [[let (tp, tm) = mfs Map.! x in (x, tp, tm) | x <- scc] | scc <- funSCCs]
      dataSCCs' = [[let (ps, cs) = mds Map.! x in (x, ps, cs) | x <- scc] | scc <- dataSCCs]
  in
    anyDupDefs ps >>
    -- TODO: maybe sort progs back into original order?
    -- Add datatype defs to environment
    inferData dataSCCs'
    -- Then check externs
      (foldr inferExtern
    -- Then check functions
         (foldr inferFuns
    -- Then check end term
            (solveM (infer end >>: curry return) >>= \ (end', tp, tgs) ->
             return (SProgs [] end')) funSCCs') es)

inferFile :: UsProgs -> Either String SProgs
inferFile ps =
  either (\ (e, loc) -> Left (show e ++ ", " ++ show loc)) (\ (a, s, w) -> Right a)
    (runExcept (runRWST (inferProgs ps)
                        (CheckR (Env mempty mempty mempty) (Loc "" "")) mempty))

