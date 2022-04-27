module TypeInf.Solve where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.RWS.Lazy
import Control.Monad.Except
import TypeInf.Check
import Util.Helpers
import Util.SCC
import Exprs
import Scope.Subst
import Scope.Free
import Scope.Name
import Show()

bindTp :: Var -> Type -> Either TypeError Subst
bindTp x tp
  | tp == TpVar x [] = Right Map.empty
  | occursCheck x tp = Left (InfiniteType x tp)
  | otherwise = Right (Map.singleton x (SubTp tp))

unify :: Type -> Type -> Either TypeError Subst
unify (TpVar y@('?' : _) []) tp = bindTp y tp -- Only substitute tag/type inst vars
unify (TpVar y@('#' : _) []) tp = bindTp y tp -- Same ^
unify tp (TpVar y@('?' : _) []) = bindTp y tp -- Same ^
unify tp (TpVar y@('#' : _) []) = bindTp y tp -- Same ^
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
      (utgs, utpvs) = Map.partition id unsolved
      fvs = freeVars (subst s rtp)
      internalUnsolved = Map.difference utpvs fvs
      s' = fmap (\ False -> SubTp tpUnit) internalUnsolved
      s'' = s' `compose` s
  in
    (s'', Map.keys (Map.intersection utpvs fvs), Map.keys utgs)

solve :: Env -> SolveVars -> Type -> [(Constraint, Loc)] -> Either (TypeError, Loc) (Subst, [Var], [Var])
solve g vs rtp cs =
  unifyAll (getUnifications cs) >>= \ s ->
  let (s', xs, tgs) = solveInternal vs s rtp in
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
  mapM (const freshTp) fs >>= \ itps ->
  let ftps = [(x, itp) | ((x, _, _), itp) <- zip fs itps] in
    inEnvs ftps
    (solvesM ftps
      (mapM (\ ((x, mtp, tm), itp) ->
               localCurDef x $
               infer tm >>: \ tm' tp' ->
               constrain (Unify itp tp') >>
               (if mtp /= NoTp then checkType mtp >>= \ mtp' -> constrain (Unify mtp' tp') else okay) >>
               return (x, tm', tp')) (zip fs itps))) >>= \ xtmstps ->
    foldr (\ (x, tm, stp) -> defTerm x DefVar stp) m xtmstps >>= \ (SProgs ps end) ->
    let ps' = map (\ (x, tm, stp) -> SProgFun x stp tm) xtmstps in
    return (SProgs (ps' ++ ps) end)

-- TODO: Make sure type params are same in recursive instantes. So disallow
-- data List a = Nil | Cons a (List Bool);
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

    checkData :: (Var, [Var], [Ctor]) -> CheckM (Var, [Var], [Ctor])
    checkData (y, ps, cs) =
      defParams ps (mapM checkCtor cs) >>= \ cs' ->
      return (y, ps, cs')

    addDefs :: [(Var, [Var], [Var], [Ctor])] -> CheckM SProgs -> CheckM SProgs
    addDefs [] cont = cont
    addDefs ((y, tgs, ps, cs) : ds) cont =
      defData y tgs ps cs (addDefs ds cont) >>= \ (SProgs sps etm) ->
      return (SProgs (SProgData y tgs ps cs : sps) etm)

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
      listenSolveVars
        (foldl
           (\ m (y, ps, cs) -> defType y [] ps cs m)
           (freshTagVar >> mapM checkData dscc)
           dscc)
        >>= \ (dscc', vs) ->
      let tgs = Map.keys (Map.filter id vs)
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

inferEnd :: UsTm -> CheckM SProgs
inferEnd end =
  solveM (infer end >>: curry return) >>= \ (end', tp, tgs) ->
  return (SProgs [] end')

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

inferFile :: UsProgs -> Either String SProgs
inferFile ps =
  either (\ (e, loc) -> Left (show e ++ ", " ++ show loc)) (\ (a, s, w) -> Right a)
    (runExcept (runRWST (inferProgs ps)
                        (CheckR (Env mempty mempty mempty) (Loc "" "")) mempty))

