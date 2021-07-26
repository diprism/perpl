module Check where
import Ctxt
import Free
import Exprs
import Util
import Name

--            (message, history)
type ErrMsg = (String, [String])

-- TODO: make sure x occurs same number of times in each branch of computation
--       (e.g. case q of false -> q | true -> false)
checkAffLin :: Var -> Type -> UsTm -> Bool
checkAffLin x (TpArr _ _) tm = isAff x tm
checkAffLin x _ tm = True

-- Return error
err :: String -> Either ErrMsg a
err msg = Left (msg, [])

-- Error if b is true
ifErr :: Bool -> String -> Either ErrMsg ()
ifErr b e = if b then err e else okay

-- Error if x \in g
--ifBound :: Ctxt -> Var -> Either ErrMsg ()
--ifBound g x = ifErr (ctxtBinds g x) ("'" ++ x ++ "' has multiple definitions")
ifBound :: [Var] -> Var -> Either ErrMsg ()
ifBound ds x = ifErr (x `elem` ds) ("'" ++ x ++ "' has multiple definitions")


-- Error message prefix, telling which definition an error occurred in
declErr :: Var -> Either ErrMsg a -> Either ErrMsg a
declErr x = mapLeft $ \ (s, h) -> (s, h ++ [("In the definition of " ++ x ++ ", ")])

pickErrHist :: Either ErrMsg a -> Either String a
pickErrHist = mapLeft $ \ (s, h) -> concat (take 2 (reverse h)) ++ s

-- Check and elaborate a term under a context
checkTerm :: Ctxt -> UsTm -> Either ErrMsg (Term, Type)
checkTermh :: Ctxt -> UsTm -> Either ErrMsg Term

-- Checks and elaborates a term variable, if it is one
checkTermVar :: Bool -> Ctxt -> UsTm -> Either ErrMsg Term
checkTermVar eta g (UsVar x) = maybe2 (ctxtLookupTerm g x)
  (err ("Variable '" ++ x ++ "' not in scope"))
  $ \ (sc, tp) -> case (eta, sc) of
    (_, ScopeLocal) -> return (TmVarL x tp)
    (True, sc) ->
      let (tps, TpVar y) = splitArrows tp in
        return (etaExpand (if sc == ScopeGlobal then DefVar else CtorVar) x [] (getArgs x tps) (TpVar y))
    (False, sc) -> return (TmVarG (if sc == ScopeGlobal then DefVar else CtorVar) x [] tp)
checkTermVar eta g tm = checkTermh g tm

checkTerm g tm =
  mapLeft (\ (s, h) -> (s, ("in the term " ++ show tm ++ ": ") : h))
    (checkTermh g tm) >>= \ tm' ->
  return (tm', getType tm')

checkTermh g (UsVar x) = checkTermVar True g (UsVar x)

checkTermh g (UsLam x tp tm) =
  ifErr (not $ checkAffLin x tp tm)
    ("Bound variable '" ++ x ++ "' is not affine in the body") >>
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
      ifErr (length as > length tps) numErrMsg >>
      let tps' = take (length as) tps
          end' = joinArrows (drop (length as) tps) end in
      sequence (map (checkTerm g) as) >>= \ as' ->
      sequence (map (\ ((a, atp), tp) -> ifErr (atp /= tp) (expVsActTpMsg tp atp)) (zip as' tps')) >>
      case hd' of
        (TmVarG gv x [] tp) ->
          let etas = getArgs x tps
              etas' = drop (length as') etas in
          return (etaExpand gv x as' etas' end)
          --return (joinApps (etaExpand x [] etas y) as' end')
        _ -> return (joinApps hd' as')

checkTermh g (UsCase tm cs) =
  checkTerm g tm >>= \ (tm', tp) ->
  case tp of
    (TpArr _ _) -> err "Case splitting on arrow type"
    (TpVar y) -> maybe2 (ctxtLookupType g y)
      (err "Error in checkTerm UsCase") -- shouldn't happen
      $ \ ycs -> checkCases g ycs (sortCases ycs cs) >>= \ (cs', tp') ->
        return (TmCase (TmFold False tm' (TpVar y)) (TpVar y) cs' tp')

checkTermh g (UsSamp d tp) =
  checkType g tp >>
  return (TmSamp d tp)

checkTermh g (UsLet x ltm tm) =
  checkTerm g ltm >>= \ (ltm', ltp) ->
  checkTerm (ctxtDeclTerm g x ltp) tm >>= \ (tm', tp) ->
  ifErr (not $ checkAffLin x ltp tm)
    ("Bound variable '" ++ x ++ "' is not affine in the body") >>
  return (TmLet x ltm' ltp tm' tp)

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
checkType :: Ctxt -> Type -> Either ErrMsg ()

checkType g (TpVar y) = maybe2 (ctxtLookupType g y)
  (err ("Type variable '" ++ y ++ "' not in scope"))
  $ \ cs -> okay

checkType g (TpArr tp1 tp2) =
  checkType g tp1 >>
  checkType g tp2

-- Check and elaborate a case under a context
checkCase :: Ctxt -> Ctor -> CaseUs -> Either ErrMsg (Case, Type)
checkCase g (Ctor x as) (CaseUs x' as' tm) =
  ifErr (x /= x') ("Expected case '" ++ x ++ "' but got '" ++ x' ++ "'") >>
  ifErr (length as /= length as')
    ("Expected " ++ show (length as) ++ " args for case '" ++
      x ++ "', but got " ++ show (length as')) >>
  let g' = ctxtDeclArgs g (zip as' as)
      as'' = zip as' as
      msg = \ a -> "In the case " ++ x' ++ ", arg " ++ a ++ " is not linear in the body" in
  foldr (\ (a, atp) r -> ifErr (not $ checkAffLin a atp tm) (msg a) >> r) okay as'' >>
  checkTerm g' tm >>= \ (tm', tp) ->
  return (Case x as'' tm', tp)

-- Check and elaborate a list of cases under a context
checkCases :: Ctxt -> [Ctor] -> [CaseUs] -> Either ErrMsg ([Case], Type)
checkCases g [] [] = err "Case splitting on empty datatype"
checkCases g (ct : cts) (c : cs) =
  checkCase g ct c >>= \ (c', tp) ->
  checkCasesh g cts cs tp >>= \ cs' ->
  return (c' : cs', tp)

-- Check and elaborate a list of cases under a context,
-- given an anticipated return type
checkCasesh :: Ctxt -> [Ctor] -> [CaseUs] -> Type -> Either ErrMsg [Case]
checkCasesh g [] [] tp = return []
checkCasesh g (ct : cts) (c : cs) tp =
  checkCase g ct c >>= \ (c', tp') ->
  ifErr (tp /= tp') "Cases have different types" >>
  checkCasesh g cts cs tp >>= \ cs' ->
  return (c' : cs')
checkCasesh g _ _ tp = err "Incorrect number of cases"

-- Check an elaborate a program under a context and a list of already-defined vars
checkProgs :: [Var] -> Ctxt -> UsProgs -> Either ErrMsg Progs
checkProgs ds g (UsProgExec tm) =
  checkTerm g tm >>= \ (tm', tp') ->
  return (Progs [] tm')

checkProgs ds g (UsProgFun x tp tm ps) =
  declErr x (ifBound ds x >> checkType g tp >> checkTerm g tm) >>= \ (tm', tp') ->
  ifErr (tp /= tp')
    ("Expected type of function '" ++ x ++ "' does not match computed type") >>
  checkProgs (x : ds) g ps >>= \ (Progs ps' end) ->
  return (Progs (ProgFun x [] tm' tp : ps') end)

checkProgs ds g (UsProgExtern x tp ps) =
  declErr x (ifBound ds x >> checkType g tp) >>
  checkProgs (x : ds) g ps >>= \ (Progs ps' end) ->
  return (Progs (ProgExtern x "0" [] tp : ps') end)

checkProgs ds g (UsProgData x cs ps) =
  declErr x (ifBound ds x >> foldr (\ (Ctor x tps) r -> r >>= \ ds -> ifBound ds x >> foldr (\ tp r -> checkType g tp >> ifErr (hasArr tp) ("Constructor " ++ x ++ " has an arg with an arrow type, which is not allowed") >> r) okay tps >> return (x : ds)) (return (x : ds)) cs) >>= \ ds' ->
  checkProgs ds' g ps >>= \ (Progs ps' end) ->
  return (Progs (ProgData x cs : ps') end)

-- Check and elaborate a file
checkFile :: UsProgs -> Either String Progs
checkFile ps = pickErrHist (checkProgs [] (ctxtDefUsProgs ps) ps)
