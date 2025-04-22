module TypeInf.Solve (inferFile) where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad (zipWithM_)
import Control.Monad.RWS.Lazy
import Control.Monad.Except
import TypeInf.Check
import Util.Helpers
import Util.Graph (scc, SCC(..))
import Struct.Lib
import Scope.Subst (Subst(tmVars, tpVars, tags), STerm(Replace), FreeVars(freeTmVars, freeTpVars), subst, freeVars, freeDatatypes, substTags)
import Scope.Free (robust, positive)
import Scope.Ctxt (Ctxt, emptyCtxt, ctxtLookupType2, ctxtAddData)

bindTp :: TpVar -> Type -> Either TypeError Subst
bindTp x tp
  -- Trying to bind x = x, so nothing needs to be done
  | tp == TpVar x = Right mempty
  -- If x occurs in tp, then substituting would lead to an infinite type
  | occursCheck x tp = Left (InfiniteType x tp)
  -- Add (x := tp) to substitution
  | otherwise = Right mempty{tpVars = Map.singleton x tp}

-- Try to unify two types
unify :: Type -> Type -> Either TypeError Subst
unify (TpVar y) tp = bindTp y tp
unify tp (TpVar y) = bindTp y tp
unify tp1@(TpData y1 tgs1 as1) tp2@(TpData y2 tgs2 as2)
  | y1 == y2 && length tgs1 == length tgs2 && length as1 == length as2 =
      unifyTags (zip tgs1 tgs2) >>= \ s ->
      unifyTypes' (zip as1 as2) >>= \ s' ->
      return (s' <> s)
  | otherwise = Left (UnificationError tp1 tp2)
unify (TpArr l1 r1) (TpArr l2 r2) =
  unify l1 l2 >>= \ sl ->
  unify (subst sl r1) (subst sl r2) >>= \ sr ->
  return (sr <> sl)
unify (TpProd am1 tps1) (TpProd am2 tps2)
  | (am1 /= am2) || (length tps1 /= length tps2) =
      Left (UnificationError (TpProd am1 tps1) (TpProd am2 tps2))
  | otherwise =
      unifyTypes' (zip tps1 tps2)
unify NoTp tp = error "unify should not receive a NoTp"
unify tp NoTp = error "unify should not receive a NoTp"
unify tp1 tp2
  | tp1 == tp2 = Right mempty
  | otherwise  = Left (UnificationError tp1 tp2)

-- For [(x1, y1), (x2, y2), ...], unify x1 and y1, unify x2 and y2, etc.
unifyTypes' :: [(Type, Type)] -> Either TypeError Subst
unifyTypes' tps = mapLeft fst $ unifyTypes [(tp1, tp2, Loc { curDef = Nothing, curExpr = ""}) | (tp1, tp2) <- tps]

-- For [(x1, y1), (x2, y2), ...], unify x1 and y1, unify x2 and y2, etc.
unifyTypes :: [(Type, Type, Loc)] -> Either (TypeError, Loc) Subst
unifyTypes =
  foldr
    (\ (tp1, tp2, l) s ->
        s >>= \ s ->
        mapLeft (\ e -> (e, l)) (unify (subst s tp1) (subst s tp2)) >>= \ s' ->
        return (s' <> s))
    (Right mempty)

unifyTag :: Tag -> Tag -> Either TypeError Subst
unifyTag x y
  | x /= y = Right mempty{tags = Map.singleton x y}
  | otherwise = Right mempty

unifyTags :: [(Tag, Tag)] -> Either TypeError Subst
unifyTags = foldr
  (\ (tg1, tg2) es -> es >>= \ s ->
                      unifyTag (subst s tg1) (subst s tg2) >>= \ s' ->
                      return (s' <> s))
  (Right mempty)

{- solvedWell e s cs xs

   Makes sure that robust-constrained solved type vars have robust solutions.
   ∀-quantifies all free type variables.

   - e: environment
   - s: the substitution found by solving the constraints
   - cs: the constraints
   - xs: free type variables

   Returns: list of ∀-quantified type variables -}

solvedWell :: Ctxt -> Subst -> [(Constraint, Loc)] -> [TpVar] -> Either (TypeError, Loc) [Forall]
solvedWell e s cs xs =
  Set.unions <$> sequence [ h (subst s c) l | (c, l) <- cs ] >>= \ rfvs ->
  -- Mark each x as robust if it appears in rfvs (used vars in robust types)
  Right [Forall x (if x `Set.member` rfvs then BoundRobust else BoundNone) | x <- xs]
  where
    -- Returns set of used variables in robust-constrained types
    h :: Constraint -> Loc -> Either (TypeError, Loc) (Set TpVar)
    h (Unify tp1 tp2) l -- Not sure if checking tp1 == tp2 is necessary, but better be safe?
      | tp1 /= tp2 = Left (ConflictingTypes tp1 tp2, l)
      | otherwise = Right mempty
    h (Robust tp) l -- Make sure that tp was solved to a robust type
      | not (robust e tp) = Left (RobustType tp, l)
      | otherwise = Right (usedVars tp) -- all used vars in tp must end up robust too
    h (Positive tp) l -- Make sure that tp was solved to a robust type
      | not (positive e tp) = Left (PositiveType tp, l)
      | otherwise = Right (usedVars tp) -- all used vars in tp must end up robust too

    -- Can assume tp is robust
    usedVars :: Type -> Set TpVar
    usedVars (TpData y [] as) = case ctxtLookupType2 e y of
      Just ([], ps, cs) ->
        let s = mempty{tpVars = Map.fromList (pickyZip ps as)} in
        Set.unions [usedVars (subst s ca) | Ctor _ cas <- cs, ca <- cas]
      _ -> error "this shouldn't happen"
    usedVars (TpVar x) = Set.singleton x
    usedVars (TpProd Multiplicative tps) = Set.unions (usedVars <$> tps)
    usedVars _ = error "this shouldn't happen either"

-- If in the process of doing type inference on a term,
-- it introduced some type vars that don't appear in the
-- return type, simply solve those internal vars to Zero type
-- Example: `let f = \ x. x in True`
-- Returns (new subst, remaining type vars, remaining tag vars)
solveInternal :: SolveVars -> Subst -> Type -> (Subst, [Tag], [TpVar])
solveInternal (tgs, tpvs) s rtp =
  let utgs  = Set.difference tgs  (Map.keysSet (tags   s))
      utpvs = Set.difference tpvs (Map.keysSet (tpVars s))
      fvs = Map.keysSet (freeTpVars (freeVars (subst s rtp))) -- get vars that occur in the return type
      internalUnsolved = Set.difference utpvs fvs
      s' = mempty{tpVars = Map.fromSet (const tpZero) internalUnsolved} -- substitute with Zero
      s'' = s' <> s -- Add to Zero substitutions to s
  in
    (s'', Set.toList utgs, Set.toList (Set.intersection utpvs fvs))

{- solve g vs rtp cs

Tries to solve a set of constraints
  - g:   type environment
  - vs:  the variables to solve
  - rtp: type whose free vars are allowed to remain unsolved
  - cs:  List of constraints

If no error, returns (solution subst, remaining tag vars, remaining type vars)
-}

solve :: Ctxt -> SolveVars -> Type -> [(Constraint, Loc)] -> Either (TypeError, Loc) (Subst, [Tag], [Forall])
solve g vs rtp cs =
  unifyTypes (getUnifications cs) >>= \ s ->
  let (s', tgs, xs) = solveInternal vs s rtp in
  solvedWell g s' cs xs >>= \ xs' ->
  return (s', tgs, xs')

{- solveM m

Solves the constraints generated in m, and arbitrarily solves all remaining type vars as Zero. (Tags may remain, though.)

m is a CheckM returning the term to be solved

Returns: (tm, tp, tgs), where
- tm: the solved term
- tp: its type
- tgs: list of remaining tags -}

solveM :: CheckM Term -> CheckM (Term, Type, [Tag])
solveM m =
  listenSolveVars (listen m) >>= \ ((a, cs), vs) ->
  -- Because we use NoTp below, there are no FVs in the type, so all
  -- remaining type vars are seen as internal unsolved and become Zero
  askEnv >>= \ g ->
  case solve g vs NoTp cs of
    Left e -> throwError e
    Right (s, tgs, []) -> return (subst s a, subst s (typeof a), tgs)
    Right _ -> error "type variables remaining after solving (this shouldn't happen)"

{- solvesM ms

ms is a CheckM returning [(x1, tm1, tp1), ...], which is a list of
(possibly mutually recursive) global function definitions.

Returns: [(x1, tm1, tgs1, ps1, tp1)], where
- x: the left-hand side of the definition
- tm: the right-hand side term
- tgs: tag variables
- ps: type variables
- tp: the type of tm -}

solvesM :: CheckM [(TmName, Term, Type)] -> CheckM [(TmName, Term, [Tag], [Forall], Type)]
solvesM ms =
  listenSolveVars (listen ms) >>= \ ((defs, cs), vs) ->
  askEnv >>= \ g ->
  case solve g vs (TpProd Multiplicative [tp | (_, _, tp) <- defs]) cs of
    Left e -> throwError e
    Right (s, tgs, xs) ->
      let
        -- Perform type substitutions (s) and add type/tag parameters.
        defs' = map (\ (f, tm, tp) ->
                        let tm' = subst s tm
                            tp' = subst s tp
                            xs' = [Forall x r | Forall x r <- xs, x `Map.member` freeTpVars (freeVars tp')]
                        in
                          (f, tm', tgs, xs', tp')) defs
        -- Add tag/type parameters to right-hand side terms. This has
        -- to be done in a second pass because of mutual recursion.
        -- This substitution is possible because occurrences of f are actually
        -- local variables (TmVarL); they change into global variables (TmVarG) now.
        s' = mempty{tmVars = Map.fromList [(tmNameToVar f, Replace (TmVarG GlDefine f tgs [TpVar x | Forall x r <- xs'] [] tp')) | (f, _, tgs, xs', tp') <- defs']}
        defs'' = [(f, subst s' tm', tgs, xs', tp') | (f, tm', tgs, xs', tp') <- defs']
      in
        return defs''


{- Creates graphs of function dependencies and datatype dependencies in
a program.  The nodes of the function dependency graph are the defines
(not externs), and there is an edge from every define to every define
that it uses. Similarly for the datatype dependency graph. -}

getFunDeps :: UsProgs -> Map TmName (Set TmName)
getFunDeps (UsProgs ps end) = clean (foldr h mempty ps)
  where
    -- Removes ctors, externs, type parameters from each set in the map
    clean :: Map TmName (Set TmName) -> Map TmName (Set TmName)
    clean m = let s = Map.keysSet m in fmap (Set.intersection s) m

    -- Create an edge from every define lhs to its rhs's
    -- free vars.  The free vars include many kinds of variables, but
    -- we only care about the defines.
    h :: UsProg -> Map TmName (Set TmName) -> Map TmName (Set TmName)
    h (UsProgDefine x tm mtp) deps =
      Map.insert x (Set.mapMonotonic tmVarToName (Map.keysSet (freeTmVars (freeVars tm)))) deps
    h _ deps = deps

getDataDeps :: UsProgs -> Map TpName (Set TpName)
getDataDeps (UsProgs ps end) = foldr h mempty ps
  where
    h :: UsProg -> Map TpName (Set TpName) -> Map TpName (Set TpName)
    h (UsProgData y ps cs) deps =
      Map.insert y (Set.unions [freeDatatypes tp | Ctor _ tps <- cs, tp <- tps]) deps
    h _ deps = deps

-- Helper for splitProgs
splitProgsH :: UsProg -> ([(TmName, Type, UsTm)], [(TmName, Type)], [(TpName, [TpVar], [Ctor])])
splitProgsH (UsProgDefine x tm mtp) = ([(x, mtp, tm)], [], [])
splitProgsH (UsProgExtern x tp) = ([], [(x, tp)], [])
splitProgsH (UsProgData y ps cs) = ([], [], [(y, ps, cs)])

-- Splits a program up into (functions, externs, datatypes)
splitProgs :: UsProgs -> ([(TmName, Type, UsTm)], [(TmName, Type)], [(TpName, [TpVar], [Ctor])], UsTm)
splitProgs (UsProgs ps end) =
  let (fs, es, ds) = foldr (\ p (fs, es, ds) ->
                               let (fs', es', ds') = splitProgsH p in
                                 (fs' ++ fs, es' ++ es, ds' ++ ds))
                           ([], [], []) ps in
    (fs, es, ds, end)

-- Infers a set of mutually-defined global functions,
-- adding their inferred types to the env when inferring
-- the rest of the program, and adding their defs to the returned (schemified) program
inferFuns :: SCC (TmName, Type, UsTm) -> CheckM SProgs -> CheckM SProgs
inferFuns (TrivialSCC f) = inferFuns' [f]
inferFuns (NontrivialSCC fs) = inferFuns' fs

inferFuns' :: [(TmName, Type, UsTm)] -> CheckM SProgs -> CheckM SProgs
inferFuns' fs m =
  -- Get a fresh type var for each function in fs
  mapM (const freshTp) fs >>= \ itps ->
  -- ftps is the set of function names with their type (var)
  let ftps = [(tmNameToVar x, itp) | ((x, _, _), itp) <- zip fs itps] in
    -- add ftps to env as local variables (CtLocal) for now;
    -- they will be changed to global variables inside solvesM
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
    foldr (\ (x, tm, tgs, ps, tp) -> defGlobal x tgs ps tp) m xtmstps >>= \ (SProgs ps end) ->
    -- Add defs to returned (schemified) program
    let ps' = map (\ (x, tm, tgs, ps, tp) -> SProgDefine x tgs ps tm tp) xtmstps in
    return (SProgs (ps' ++ ps) end)

{- inferData dsccs cont

Infers all datatypes in dsccs:

  - guards against polymorphic type recursion
  - adds a tag variable to each recursive datatype; this tag variable
    also propagates to every type that uses it
  - add each datatype def to env for inferring the rest of the program
  - add each datatype def to the returned (schemified) program -}

inferData :: [SCC (TpName, [TpVar], [Ctor])] -> CheckM SProgs -> CheckM SProgs
inferData dsccs cont = foldr h cont dsccs
  where
    -- Check with hPerhapsRec and add defs to returned (schemified) program
    h :: SCC (TpName, [TpVar], [Ctor]) -> CheckM SProgs -> CheckM SProgs
    h dscc cont =
      hPerhapsRec dscc >>= \ dscc' ->
      addDefs dscc' cont

    -- Helper wrapper: if recursive, use hRec; otherwise, use hNonRec
    hPerhapsRec :: SCC (TpName, [TpVar], [Ctor]) -> CheckM [(TpName, [Tag], [TpVar], [Ctor])]
    hPerhapsRec (TrivialSCC ypscs) = hNonRec ypscs
    hPerhapsRec (NontrivialSCC dscc) = hRec dscc

    -- Like checkType for datatypes
    checkData :: (TpName, [TpVar], [Ctor]) -> CheckM (TpName, [TpVar], [Ctor])
    checkData (y, ps, cs) =
      localCurDef y $
      local (\g -> g {checkEnv = foldr (\ (TpV z) g -> ctxtAddData g (TpN z) [] [] []) (checkEnv g) ps})
        (mapCtorsM checkType cs) >>= \ cs' ->
      return (y, ps, cs')

    -- Adds datatype defs and ctors to env, and adds them to returned
    -- (schemified) program
    addDefs :: [(TpName, [Tag], [TpVar], [Ctor])] -> CheckM SProgs -> CheckM SProgs
    addDefs [] cont = cont
    addDefs ((y, tgs, ps, cs) : ds) cont =
      defData y tgs ps cs (addDefs ds cont) >>= \ (SProgs sps etm) ->
      return (SProgs (SProgData y tgs ps cs : sps) etm)

    -- Handles checking a single, non-recursive datatype
    -- Input: a singleton (datatype name, type param names, constructors)
    -- Return: a singleton (datatype name, tag vars, type param names, constructors)
    hNonRec :: (TpName, [TpVar], [Ctor]) -> CheckM [(TpName, [Tag], [TpVar], [Ctor])]
    hNonRec (y, ps, cs) =
      listenSolveVars (checkData (y, ps, cs)) >>= \ ((_, _, cs'), (tgs, _)) ->
        return [(y, Set.toList tgs, ps, cs')]

    -- The remaining functions are for the recursive case.

    -- Each time a datatype in the SCC is used, add a constraint
    -- unifying the actual type parameters with the formal type
    -- parameters in the datatype's definition. In other words, the
    -- types in the SCC are not yet polymorphic. This prevents
    -- datatypes like
    --     data FullBinaryTree a = Leaf | FullBinaryTree (a, a)
    constrainData :: (TpName, [TpVar], [Ctor]) -> CheckM ()
    constrainData (y, ps, cs) = localCurDef y (mapCtorsM_ constrainTpApps cs)
    constrainTpApps :: Type -> CheckM ()
    constrainTpApps (TpArr tp1 tp2) = constrainTpApps tp1 >> constrainTpApps tp2
    constrainTpApps (TpVar y) = return ()
    constrainTpApps (TpData y [] as) =
      lookupDatatype y >>= \ (_, ps, _) ->
        guardM (length ps == length as) (WrongNumArgs (length ps) (length as)) >>
        zipWithM_ (\ x a -> constrain (Unify (TpVar x) a)) ps as
    constrainTpApps (TpData y tgs as) =
      error "constrainTpApps wasn't expecting to see tags"
    constrainTpApps (TpProd am tps) = mapM_ constrainTpApps tps
    constrainTpApps NoTp = error "this shouldn't happen"

    -- Solve constraints, but don't actually perform the
    -- substitutions in the solution.
    solveDataSCC :: CheckM a -> CheckM ()
    solveDataSCC m =
      listenSolveVars (listen m) >>= \ ((dscc, cs), vs@(_, tpvs)) ->
      askEnv >>= \ g ->
      either
        throwError
        (\ (s, tgs, xs) -> return ())
        (solve g vs (TpProd Multiplicative [TpVar v | v <- Set.toList tpvs]) cs)

    -- Like defType, but for a list of datatypes. This lets all the
    -- datatypes in the SCC see one another in the type environment.
    defDataSCC :: [(TpName, [TpVar], [Ctor])] -> CheckM a -> CheckM a
    defDataSCC dscc m =
      foldl (\ m (y, ps, cs) -> defData y [] ps [] m) m dscc

    -- Handles checking mutually-recursive datatypes
    -- Input: a list of (datatype name, type param names, constructors)
    -- Return: a list of (datatype name, tag vars, type param names, constructors)
    hRec :: [(TpName, [TpVar], [Ctor])] -> CheckM [(TpName, [Tag], [TpVar], [Ctor])]
    hRec dscc =
      -- Check all the datatype definitions.
      listenSolveVars
        (defDataSCC dscc
           (freshTagVar >> mapM checkData dscc))
        >>= \ (dscc', (tgs, _)) ->
      -- Infer type variables, which amounts to just checking that a
      -- type doesn't recursively use itself with different
      -- parameters.
      solveDataSCC
        -- type variables ps have already been renamed apart in alphaRenameProgs
        (mapM_ (\ (y, ps, cs) -> mapM_ addSolveTpVar ps) dscc >>
         defDataSCC dscc (mapM_ constrainData dscc)) >>
      -- Add tag vars in vs to the recursive uses of types in dscc
      -- by substituting y := y tgs.
      
      let s = Map.fromList [(y, Set.toList tgs) | (y, ps, cs) <- dscc']
      in
        return [(y, Set.toList tgs, ps, mapCtors (substTags s) cs) | (y, ps, cs) <- dscc']


-- Checks an extern declaration
inferExtern :: (TmName, Type) -> CheckM SProgs -> CheckM SProgs
inferExtern (x, tp) m =
  -- It's possible that checkType tp introduces new tag variables,
  -- but only within an unused type parameter, so it's safe to ignore them.
  localCurDef x (checkType tp) >>= \ tp' ->
  -- Make sure tp' doesn't use any recursive datatypes
  localCurDef x (guardExternRec tp') >>
  -- Add (x : tp') to env, checking rest of program
  defExtern x tp' m >>= \ (SProgs ps end) ->
  -- Add (extern x : tp') to returned program
  return (SProgs (SProgExtern x tp' : ps) end)

-- Checks the end term (start term? Should be consistent with name...)
inferEnd :: UsTm -> CheckM SProgs
inferEnd end =
  let m = infer end in
  solveM m >>= \ (end', tp, tgs) ->
  return (SProgs [] end')

-- Infers an entire program, returning a schemified, elaborated one
inferProgs :: UsProgs -> CheckM SProgs
inferProgs ps =
  let fdeps = getFunDeps ps
      ddeps = getDataDeps ps
      (fs, es, ds, end) = splitProgs ps
      mfs = Map.fromList [(x, (tp, tm)) | (x, tp, tm) <- fs]
      mds = Map.fromList [(x, (ps, cs)) | (x, ps, cs) <- ds]
      -- sccs is a list of strongly connected functions.
      -- you can check it in order, by checking together
      -- all the functions in each strongly connected set
      funSCCs   = scc fdeps
      dataSCCs  = scc ddeps
      funSCCs'  = map (fmap (\x -> let (tp, tm) = mfs Map.! x in (x, tp, tm))) funSCCs
      dataSCCs' = map (fmap (\x -> let (ps, cs) = mds Map.! x in (x, ps, cs))) dataSCCs
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
  either (\ (e, loc) -> Left (if null (show loc) then show e else show e ++ ", " ++ show loc))
         (\ (a, s, w) -> Right a)
    (runExcept (runRWST (inferProgs ps)
                        (CheckR emptyCtxt (Loc Nothing "")) mempty))
