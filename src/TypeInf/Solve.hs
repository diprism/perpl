module TypeInf.Solve where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.RWS.Lazy
import Control.Monad.Except
import TypeInf.Check
import Util.Helpers
import Util.SCC
import Struct.Lib
import Scope.Subst
import Scope.Free
import Scope.Name
import Scope.Ctxt

bindTp :: Var -> Type -> Either TypeError Subst
bindTp x tp
  -- Trying to bind x = x, so nothing needs to be done
  | tp == TpVar x [] = Right Map.empty
  -- If x occurs in tp, then substituting would lead to an infinite type
  | occursCheck x tp = Left (InfiniteType x tp)
  -- Add (x := tp) to substitution
  | otherwise = Right (Map.singleton x (SubTp tp))

-- Try to unify two types
unify :: Type -> Type -> Either TypeError Subst
unify (TpVar y@('?' : _) []) tp = bindTp y tp -- Only substitute tag/type inst vars
unify (TpVar y@('#' : _) []) tp = bindTp y tp -- Same ^
unify tp (TpVar y@('?' : _) []) = bindTp y tp -- Same ^
unify tp (TpVar y@('#' : _) []) = bindTp y tp -- Same ^
unify tp1@(TpVar y1 as1) tp2@(TpVar y2 as2)
  | y1 == y2 && length as1 == length as2 =
      unifyAll' (zip as1 as2)
  | otherwise = Left (UnificationError tp1 tp2)
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

-- For [(x1, y1), (x2, y2), ...], unify x1 and y1, unify x2 and y2, etc.
unifyAll' :: [(Type, Type)] -> Either TypeError Subst
unifyAll' tps = mapLeft fst $ unifyAll [(tp1, tp2, Loc { curDef = "", curExpr = ""}) | (tp1, tp2) <- tps]

-- For [(x1, y1), (x2, y2), ...], unify x1 and y1, unify x2 and y2, etc.
unifyAll :: [(Type, Type, Loc)] -> Either (TypeError, Loc) Subst
unifyAll =
  foldr
    (\ (tp1, tp2, l) s ->
        s >>= \ s ->
        mapLeft (\ e -> (e, l)) (unify (subst s tp1) (subst s tp2)) >>= \ s' ->
        return (s' `compose` s))
    (Right Map.empty)

-- Makes sure that robust-constrained solved type vars have robust solutions
solvedWell :: Env -> Subst -> [(Constraint, Loc)] -> Either (TypeError, Loc) ()
solvedWell e s cs = sequence [ h (subst s c) l | (c, l) <- cs ] >> okay where
  robust' = robust (fmap (\ (tgs, ps, cs) -> DefData (tgs++ps) cs) (typeEnv e))

  h (Unify tp1 tp2) l -- Not sure if checking tp1 == tp2 is necessary, but better be safe?
    | tp1 /= tp2 = Left (ConflictingTypes tp1 tp2, l)
    | otherwise = okay
  h (Robust tp) l -- Make sure that tp was solved to a robust type
    | not (robust' tp) = Left (RobustType tp, l)
    | otherwise = okay

-- If in the process of doing type inference on a term,
-- it introduced some type vars that don't appear in the
-- return type, simply solve those internal vars to Unit
-- Example: `let f = \ x. x in True`
-- Returns (new subst, remaining type vars, remaining tag vars)
solveInternal :: SolveVars -> Subst -> Type -> (Subst, [Var], [Var])
solveInternal vs s rtp =
  let unsolved = Map.difference vs s
      (utgs, utpvs) = Map.partition id unsolved -- split into tag and type vars
      fvs = freeVars (subst s rtp) -- get vars that occur in the return type
      internalUnsolved = Map.difference utpvs fvs
      s' = fmap (\ False -> SubTp tpUnit) internalUnsolved -- substitute for Unit
      s'' = s' `compose` s -- Add to Unit substitutions to s
  in
    (s'', Map.keys (Map.intersection utpvs fvs), Map.keys utgs)

{- solve g vs rtp cs

Tries to solve a set of constraints
  - g:   type environment
  - vs:  the variables to solve
  - rtp: type whose free vars are allowed to remain unsolved
  - cs:  List of constraints

If no error, returns (solution subst, remaining type vars, remaining tag vars)
-}

solve :: Env -> SolveVars -> Type -> [(Constraint, Loc)] -> Either (TypeError, Loc) (Subst, [Var], [Var])
solve g vs rtp cs =
  unifyAll (getUnifications cs) >>= \ s ->
  let (s', xs, tgs) = solveInternal vs s rtp in
  solvedWell g s' cs >>
  return (s', xs, tgs)

-- Solves constraints, and arbitrarily solves all remaining type vars as Unit
-- (tags may remain though)
-- Returns (term, its type, remaining tags)
solveM :: CheckM Term -> CheckM (Term, Type, [Var]) -- [Var] is list of tags
solveM m =
  listenSolveVars (listen m) >>= \ ((a, cs), vs) ->
  -- Because we use NoTp below, there are no FVs in the type, so all
  -- remaining type vars are seen as internal unsolved and become Unit
  askEnv >>= \ g ->
  either throwError (\ (s, [], tgs) -> return (subst s a, subst s (typeof a), tgs))
    (solve g vs NoTp cs)

-- 
solvesM :: CheckM [(Var, Term, Type)] -> CheckM [(Var, Term, Scheme)]
solvesM ms =
  listenSolveVars (listen ms) >>= \ ((atps, cs), vs) ->
  let (fs, as, tps) = unzip3 atps in
  askEnv >>= \ g ->
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
    (solve g vs (TpProd Multiplicative tps) cs)

-- Creates graphs of function dependencies and datatype dependencies in a program
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

-- Helper for splitProgsH
splitProgsH :: UsProg -> ([(Var, Type, UsTm)], [(Var, Type)], [(Var, [Var], [Ctor])])
splitProgsH (UsProgFun x mtp tm) = ([(x, mtp, tm)], [], [])
splitProgsH (UsProgExtern x tp) = ([], [(x, tp)], [])
splitProgsH (UsProgData y ps cs) = ([], [], [(y, ps, cs)])

-- Splits a program up into (functions, externs, datatypes)
splitProgs :: UsProgs -> ([(Var, Type, UsTm)], [(Var, Type)], [(Var, [Var], [Ctor])], UsTm)
splitProgs (UsProgs ps end) =
  let (fs, es, ds) = foldr (\ p (fs, es, ds) ->
                               let (fs', es', ds') = splitProgsH p in
                                 (fs' ++ fs, es' ++ es, ds' ++ ds))
                           ([], [], []) ps in
    (fs, es, ds, end)

-- Infers a set of mutually-defined global functions,
-- adding their inferred types to the env when inferring
-- the rest of the program, and adding their defs to the returned (schemified) program
inferFuns :: [(Var, Type, UsTm)] -> CheckM SProgs -> CheckM SProgs
inferFuns fs m =
  -- Get a fresh type var for each function in fs
  mapM (const freshTp) fs >>= \ itps ->
  -- ftps is the set of function names with their type (var)
  let ftps = [(x, itp) | ((x, _, _), itp) <- zip fs itps] in
    -- add ftps to env
    inEnvs ftps
    (solvesM
      (mapM (\ ((x, mtp, tm), itp) ->
               -- set location's current def to x
               localCurDef x $
               infer tm >>= \ tm' ->
               -- Constraint: itp = (typeof tm')
               constrain (Unify itp (typeof tm')) >>
               (if mtp /= NoTp then
                  checkType mtp >>= \ mtp' ->
                  -- Constraint: mtp' = (typeof tm')
                  constrain (Unify mtp' (typeof tm'))
                else
                  -- No annotation on the function definition, so just use itp
                  okay) >>
               return (x, tm', typeof tm')) (zip fs itps))) >>= \ xtmstps ->
    -- Add defs to env, and check remaining progs (m)
    foldr (\ (x, tm, stp) -> defTerm x DefVar stp) m xtmstps >>= \ (SProgs ps end) ->
    -- Add defs to returned (schemified) program
    let ps' = map (\ (x, tm, stp) -> SProgFun x stp tm) xtmstps in
    return (SProgs (ps' ++ ps) end)

{- inferData dsccs cont

Infers all datatypes in dsccs:

  - guards against polymorphic type recursion
  - adds a tag variable to each recursive datatype; this tag variable
    also propagates to every type that uses it
  - add each datatype def to env for inferring the rest of the program
  - add each datatype def to the returned (schemified) program -}

inferData :: [[(Var, [Var], [Ctor])]] -> CheckM SProgs -> CheckM SProgs
inferData dsccs cont = foldr h cont dsccs
  where
    -- Check with hPerhapsRec and add defs to returned (schemified) program
    h :: [(Var, [Var], [Ctor])] -> CheckM SProgs -> CheckM SProgs
    h dscc cont =
      hPerhapsRec dscc >>= \ dscc' ->
      addDefs dscc' cont

    -- Helper wrapper: if recursive, use hRec; otherwise, use hNonRec
    hPerhapsRec :: [(Var, [Var], [Ctor])] -> CheckM [(Var, [Var], [Var], [Ctor])]
    hPerhapsRec dscc = if sccIsRec dscc then hRec dscc else hNonRec dscc

    -- Returns if an scc (strongly-connected component) is (mutually) recursive
    -- Non-recursive only if the scc is a singleton that is itself non-recursive
    -- If the scc has 2+ datatypes, they must be mutually recursive
    sccIsRec :: [(Var, [Var], [Ctor])] -> Bool
    sccIsRec [(y, ps, cs)] = Map.member y (freeVars cs)
    sccIsRec _ = True -- Mutually-recursive datatypes are recursive

    -- Like checkType for datatypes
    checkData :: (Var, [Var], [Ctor]) -> CheckM (Var, [Var], [Ctor])
    checkData (y, ps, cs) =
      defParams ps (mapCtorsM checkType cs) >>= \ cs' ->
      return (y, ps, cs')

    -- Adds datatype defs and ctors to env, and adds them to returned
    -- (schemified) program
    addDefs :: [(Var, [Var], [Var], [Ctor])] -> CheckM SProgs -> CheckM SProgs
    addDefs [] cont = cont
    addDefs ((y, tgs, ps, cs) : ds) cont =
      defData y tgs ps cs (addDefs ds cont) >>= \ (SProgs sps etm) ->
      return (SProgs (SProgData y tgs ps cs : sps) etm)

    -- Handles checking a single, non-recursive datatype
    -- Input: a singleton (datatype name, type param names, constructors)
    -- Return: a singleton (datatype name, tag vars, type param names, constructors)
    hNonRec :: [(Var, [Var], [Ctor])] -> CheckM [(Var, [Var], [Var], [Ctor])]
    hNonRec [(y, ps, cs)] =
      listenSolveVars (checkData (y, ps, cs)) >>= \ ((_, _, cs'), vs) ->
      let tgs = Map.keys (Map.filter id vs) in
        return [(y, tgs, ps, cs')]
    hNonRec _ = error "this shouldn't happen"

    -- The remaining functions are for the recursive case.

    -- Make the type variables solvable.
    freshenTypeParams :: (Var, [Var], [Ctor]) -> CheckM (Var, [Var], [Ctor])
    freshenTypeParams (y, ps, cs) =
      -- to do: if TpVar is split into TpVar and TpData, can simply do this,
      -- since type variables have already been renamed apart in alphaRenameProgs.
      --mapM (\p -> modify (Map.insert p False)) ps >> return (y, ps, cs)
      mapM (const freshTpVar) ps >>= \ ps' ->
      let cs' = subst (Map.fromList (zipWith (\p p' -> (p, SubVar p')) ps ps')) cs in
      return (y, ps', cs')

    -- Each time a datatype in the SCC is used, add a constraint
    -- unifying the actual type parameters with the formal type
    -- parameters in the datatype's definition. In other words, the
    -- types in the SCC are not yet polymorphic. This prevents
    -- datatypes like
    --     data FullBinaryTree a = Leaf | FullBinaryTree (a, a)
    constrainData :: (Var, [Var], [Ctor]) -> CheckM ()
    constrainData (y, ps, cs) = localCurDef y (mapCtorsM_ constrainTpApps cs)
    constrainTpApps :: Type -> CheckM ()
    constrainTpApps tp@(TpArr tp1 tp2) = constrainTpApps tp1 >> constrainTpApps tp2
    constrainTpApps tp@(TpVar y as) =
      -- to do: if TpVar is split into TpVar and TpData, this can be simplified
      askEnv >>= \ g ->
      case Map.lookup y (typeEnv g) of
        Nothing -> return () -- unification variable
        Just (tgs, xs, cs) -> -- type application
          zipWithM_ (\ x a -> constrain (Unify (TpVar x []) a)) xs as
    constrainTpApps tp@(TpProd am tps) = mapM_ constrainTpApps tps
    constrainTpApps NoTp = error "this shouldn't happen"

    -- Solve constraints, but don't actually perform the
    -- substitutions in the solution.
    solveDataSCC :: CheckM a -> CheckM ()
    solveDataSCC m =
      listenSolveVars (listen m) >>= \ ((dscc, cs), vs) ->
      askEnv >>= \ g ->
      either
        throwError
        (\ (s, xs, tgs) -> return ())
        (solve g vs (TpProd Multiplicative [TpVar v [] | v <- Map.keys vs]) cs)

    -- Like defType, but for a list of datatypes. This lets all the
    -- datatypes in the SCC see one another in the type environment.
    defDataSCC :: [(Var, [Var], [Ctor])] -> CheckM a -> CheckM a
    defDataSCC dscc m =
      foldl (\ m (y, ps, cs) -> defType y [] ps cs m) m dscc

    -- Handles checking mutually-recursive datatypes
    -- Input: a list of (datatype name, type param names, constructors)
    -- Return: a list of (datatype name, tag vars, type param names, constructors)
    hRec :: [(Var, [Var], [Ctor])] -> CheckM [(Var, [Var], [Var], [Ctor])]
    hRec dscc =
      -- Infer type variables, which amounts to just checking that a
      -- type doesn't recursively use itself with different
      -- parameters.
      solveDataSCC (mapM freshenTypeParams dscc >>= \ dscc' ->
                       defDataSCC dscc' (mapM_ constrainData dscc')) >>
      -- Check all the datatype definitions.
      listenSolveVars
        (defDataSCC dscc
           (freshTagVar >> mapM checkData dscc))
        >>= \ (dscc', vs) ->
      -- Add tag vars in vs to the recursive uses of types in dscc.
      let tgs = Map.keys (Map.filter id vs)
          s = Map.fromList [(y, tgs) | (y, ps, cs) <- dscc']
      in
        return [(y, tgs, ps, mapCtors (substTags s) cs) | (y, ps, cs) <- dscc']


-- Checks an extern declaration
inferExtern :: (Var, Type) -> CheckM SProgs -> CheckM SProgs
inferExtern (x, tp) m =
  localCurDef x (checkType tp) >>= \ tp' ->
  -- Make sure tp' doesn't use any recursive datatypes
  localCurDef x (guardExternRec tp') >>
  -- Add (x : tp') to env, checking rest of program
  defTerm x DefVar (Forall [] [] tp') m >>= \ (SProgs ps end) ->
  -- Add (extern x : tp') to returned program
  return (SProgs (SProgExtern x [] tp' : ps) end)

-- Checks the end term (start term? Should be consistent with name...)
inferEnd :: UsTm -> CheckM SProgs
inferEnd end =
  -- Answer type must be robust
  let m = infer end >>= \tm -> constrain (Robust (typeof tm)) >> return tm in
  solveM m >>= \ (end', tp, tgs) ->
  return (SProgs [] end')

-- Infers an entire program, returning a schemified, elaborated one
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
            (inferEnd end) funSCCs') es)

-- Try to infer an entire file, running the CheckM monad
inferFile :: UsProgs -> Either String SProgs
inferFile ps =
  either (\ (e, loc) -> Left (show e ++ ", " ++ show loc)) (\ (a, s, w) -> Right a)
    (runExcept (runRWST (inferProgs ps)
                        (CheckR (Env mempty mempty mempty) (Loc "" "")) mempty))

