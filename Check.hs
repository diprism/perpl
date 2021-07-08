module Check where
import Ctxt
import Free
import Exprs
import Util

-- "Switch" for if we enforce linear vs. affine
checkAffLin :: Var -> UsTm -> Bool
--checkAffLin = isLin
--checkAffLinMsg = "linear"
checkAffLin = isAff
checkAffLinMsg = "affine"

-- Return error
err :: String -> Either String a
err = Left

-- Error if b is true
ifErr :: Bool -> String -> Either String ()
ifErr b e = if b then err e else okay

-- Error if x \in g
ifBound :: Ctxt -> Var -> Either String ()
ifBound g x = ifErr (ctxtBinds g x) ("'" ++ x ++ "' has multiple definitions")

-- Error message prefix, telling which definition an error occurred in
declErr :: Var -> Either String a -> Either String a
declErr x = mapLeft $ \ s -> "In the definition of '" ++ x ++ "': " ++ s

-- Check and elaborate a term under a context
checkTerm :: Ctxt -> UsTm -> Either String (Term, Type)
checkTermh :: Ctxt -> UsTm -> Either String Term

-- Checks and elaborates a term variable, if it is one
checkTermVar :: Bool -> Ctxt -> UsTm -> Either String Term
checkTermVar eta g (UsVar x) = maybe2 (ctxtLookupTerm g x)
  (err ("Variable '" ++ x ++ "' not in scope"))
  $ \ (sc, tp) -> case (eta, sc) of
    (True, ScopeCtor) ->
      let (tps, TpVar y) = splitArrows tp in
        return (ctorEtaExpand x [] (ctorGetArgs x tps) y)
    _ -> return (TmVar x tp sc)
checkTermVar eta g tm = checkTermh g tm

checkTerm g tm =
  mapLeft (\ s -> "In the term " ++ show tm ++ ": " ++ s)
    (checkTermh g tm) >>= \ tm' ->
  return (tm', getType tm')

checkTermh g (UsVar x) = checkTermVar True g (UsVar x)

checkTermh g (UsLam x tp tm) =
  ifErr (not $ checkAffLin x tm)
    ("Bound variable '" ++ x ++ "' is not " ++ checkAffLinMsg ++ " in the body") >>
  checkType g tp >>
  checkTerm (ctxtDeclTerm g x tp) tm >>= \ (tm', tp') ->
  return (TmLam x tp tm' tp')

checkTermh g (UsApp tm1 tm2) =
  let (hd, as) = splitUsApps (UsApp tm1 tm2) in
    checkTermVar False g hd >>= \ hd' ->
    let hdtp = getType hd'
        (tps, end) = splitArrows hdtp
        numErrMsg = "Expected " ++ show (length tps) ++
                    " arguments at most, but got " ++ show (length as)
        expVsActTpMsg = \ exp act -> "Expected arg of type " ++
                                     show exp ++ ", but got " ++ show act in
      ifErr (length as > length tps) (error numErrMsg) >>
      let tps' = take (length as) tps
          end' = joinArrows (drop (length as) tps) end in
      sequence (map (checkTerm g) as) >>= \ as' ->
      sequence (map (\ ((a, atp), tp) -> ifErr (atp /= tp) (expVsActTpMsg tp atp)) (zip as' tps')) >>
      case hd' of
        (TmVar x _ ScopeCtor) ->
          let TpVar y = end
              etas = ctorGetArgs x tps
              etas' = drop (length as') etas in
          return (ctorEtaExpand x as' etas' y)
          --return (joinApps (ctorEtaExpand x [] etas y) as' end')
        _ -> return (joinApps hd' as' end')

checkTermh g (UsCase tm cs) =
  checkTerm g tm >>= \ (tm', tp) ->
  case tp of
    (TpArr _ _) -> err "Case splitting on arrow type"
    (TpVar y) -> maybe2 (ctxtLookupType g y)
      (err "Error in checkTerm UsCase") -- shouldn't happen
      $ \ ycs -> checkCases g ycs cs >>= \ (cs', tp') ->
        return (TmCase tm' cs' y tp')

checkTermh g (UsSamp d tp) =
  checkType g tp >>
  return (TmSamp d tp)

{-checkTermh g (UsSamp d y) = maybe2 (ctxtLookupType g y)
  (err ("Type variable '" ++ y ++ "' not in scope"))
  $ \ cs ->
    foldr
      (\ (Ctor x as) r -> r >>
        ifErr (not $ null as)
          ("Not sure how to instantiate args for constructor '" ++ x ++ "' when sampling"))
      okay cs >>
    return (TmSamp d y)
-}


-- Check a type under a context
checkType :: Ctxt -> Type -> Either String ()

checkType g (TpVar y) = maybe2 (ctxtLookupType g y)
  (err ("Type variable '" ++ y ++ "' not in scope"))
  $ \ cs -> okay

checkType g (TpArr tp1 tp2) =
  checkType g tp1 >>
  checkType g tp2

-- Check and elaborate a case under a context
checkCase :: Ctxt -> Ctor -> CaseUs -> Either String (Case, Type)
checkCase g (Ctor x as) (CaseUs x' as' tm) =
  ifErr (x /= x') ("Expected case '" ++ x ++ "' but got '" ++ x' ++ "'") >>
  ifErr (length as /= length as')
    ("Expected " ++ show (length as) ++ " args for case '" ++
      x ++ "', but got " ++ show (length as')) >>
  let g' = ctxtDeclArgs g (zip as' as)
      msg = \ a -> "In the case " ++ x' ++ ", arg " ++ a ++ " is not linear in the body" in
  foldr (\ a r -> ifErr (not $ checkAffLin a tm) (msg a) >> r) okay as' >>
  checkTerm g' tm >>= \ (tm', tp) ->
  return (Case x (zip as' as) tm', tp)

-- Check and elaborate a list of cases under a context
checkCases :: Ctxt -> [Ctor] -> [CaseUs] -> Either String ([Case], Type)
checkCases g [] [] = err "Case splitting on empty datatype"
checkCases g (ct : cts) (c : cs) =
  checkCase g ct c >>= \ (c', tp) ->
  checkCasesh g cts cs tp >>= \ cs' ->
  return (c' : cs', tp)

-- Check and elaborate a list of cases under a context,
-- given an anticipated return type
checkCasesh :: Ctxt -> [Ctor] -> [CaseUs] -> Type -> Either String [Case]
checkCasesh g [] [] tp = return []
checkCasesh g (ct : cts) (c : cs) tp =
  checkCase g ct c >>= \ (c', tp') ->
  ifErr (tp /= tp') "Cases have different types" >>
  checkCasesh g cts cs tp >>= \ cs' ->
  return (c' : cs')


-- Check and elaborate a program under a context
checkProgs :: Ctxt -> UsProgs -> Either String Progs

checkProgs g (UsProgExec tm) =
  checkTerm g tm >>= \ (tm', tp') ->
  return (ProgExec (aff2lin g tm'))

checkProgs g (UsProgFun x tp tm ps) =
  checkType g tp >>
  declErr x (checkTerm g tm) >>= \ (tm', tp') ->
  ifErr (tp /= tp')
    ("Expected type of function '" ++ x ++ "' does not match computed type") >>
  checkProgs g ps >>= \ ps' ->
  return (ProgFun x tp (aff2lin g tm') ps')

checkProgs g (UsProgExtern x tp ps) =
  checkType g tp >>
  checkProgs g ps >>= \ ps' ->
  return (ProgExtern x tp ps')

checkProgs g (UsProgData x cs ps) =
  declErr x (foldr (\ (Ctor x tps) r -> foldr (\ tp r -> checkType g tp >> r) okay tps >> r) okay cs) >>
  checkProgs g ps >>= \ ps' ->
  return (ProgData x cs ps')


-- Traverse a program and add all defs to a contexet,
-- so that mutual definitions check correctly
declProgs :: Ctxt -> UsProgs -> Either String Ctxt

declProgs g (UsProgExec tm) = return g

declProgs g (UsProgFun x tp tm ps) =
  ifBound g x >>
  declProgs (ctxtDefTerm g x tp) ps

declProgs g (UsProgExtern x tp ps) =
  ifBound g x >>
  declProgs (ctxtDefTerm g x tp) ps

declProgs g (UsProgData y cs ps) =
  ifBound g y >>
  foldl (\ r (Ctor x tps) -> r >>= \ g' ->
            ifBound g' x >> return (ctxtDefTerm g' x (TpVar "irrelevant")))
    (return $ ctxtDeclType g y []) cs >>
  declProgs (ctxtDeclType g y cs) ps


-- Check a program, returning either an error message
-- or the elaborated program
checkFile :: UsProgs -> Either String (Ctxt, Progs)
checkFile ps = declProgs emptyCtxt ps >>= \ g' -> checkProgs g' (alphaRename g' ps) >>= \ ps' -> return (g', ps')
