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
checkAffLin :: Ctxt -> Var -> Type -> UsTm -> Either ErrMsg ()
checkAffLin g x tp tm =
  ifErr (useOnlyOnce g tp && not (isAff x tm))
    ("Bound variable '" ++ x ++ "' is not affine in the body")

-- Return error
err :: String -> Either ErrMsg a
err msg = Left (msg, [])

-- Error if b is true
ifErr :: Bool -> String -> Either ErrMsg ()
ifErr b e = if b then err e else okay

mErr :: Maybe a -> String -> Either ErrMsg a
mErr Nothing e = err e
mErr (Just a) e = Right a

-- Error if x \in g
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
checkTermVar eta g (UsVar x) =
  mErr (ctxtLookupTerm g x) ("Variable '" ++ x ++ "' not in scope") >>= \ (sc, tp) ->
  if sc == ScopeLocal then
    return (TmVarL x tp)
  else
    let vt = if sc == ScopeGlobal then DefVar else CtorVar in
      if eta then
        let (tps, end) = splitArrows tp in
          return (etaExpand vt x [] (nameParams x tps) end)
      else
        return (TmVarG vt x [] tp)
checkTermVar eta g tm = checkTermh g tm

-- Auxiliary wrapper for checkTermh
checkTerm g tm =
  mapLeft (\ (s, h) -> (s, ("in the term " ++ show tm ++ ": ") : h))
    (checkTermh g tm) >>= \ tm' ->
  return (toArg tm')

checkTermh g (UsVar x) =
  checkTermVar True g (UsVar x)

checkTermh g (UsLam x tp tm) =
  checkAffLin g x tp tm >>
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
                                     show exp ++ ", but got " ++ show act
        tps' = take (length as) tps
    in
      ifErr (length as > length tps) numErrMsg >>
      sequence [checkTerm g a | a <- as] >>= \ as' ->
      sequence [ifErr (atp /= tp) (expVsActTpMsg tp atp) | ((a, atp), tp) <- zip as' tps'] >>
      case hd' of
        (TmVarG gv x [] tp) ->
          let etas = nameParams x tps
              etas' = drop (length as') etas in
            return (etaExpand gv x as' etas' end)
        _ -> return (joinApps hd' as')

checkTermh g (UsCase tm cs) =
  checkTerm g tm >>= \ (tm', tp) ->
  case tp of
    (TpVar y) ->
      mErr (ctxtLookupType g y) "Error in checkTerm UsCase" >>= \ ycs ->
      checkCases g ycs (sortCases ycs cs) >>= \ (cs', tp') ->
      return (TmCase tm' y cs' tp')
    _ -> err "Case splitting on non-datatype"

checkTermh g (UsIf tm1 tm2 tm3) =
  checkTerm g tm1 >>= \ (tm1', tp1) ->
  checkTerm g tm2 >>= \ (tm2', tp2) ->
  checkTerm g tm3 >>= \ (tm3', tp3) ->
  ifErr (tp1 /= TpVar "Bool") "If-then-else expects the first term to be a Bool" >>
  ifErr (tp2 /= tp2) "Then- and else-cases have different types" >>
  return (TmCase tm1' "Bool" [Case "False" [] tm3', Case "True" [] tm2'] tp2)

checkTermh g (UsTmBool b) =
  return (TmVarG CtorVar (if b then "True" else "False") [] (TpVar "Bool"))

checkTermh g (UsSamp d tp) =
  checkType g tp >>
  return (TmSamp d tp)

checkTermh g (UsLet x tp ltm tm) =
  checkTerm g ltm >>= \ (ltm', ltp) ->
  checkTerm (ctxtDeclTerm g x ltp) tm >>= \ (tm', tp) ->
  checkAffLin g x ltp tm >>
  return (TmLet x ltm' ltp tm' tp)

checkTermh g (UsAmb tms) =
  mapM (checkTerm g) tms >>= \ tmtps ->
  let (tms, tps) = unzip tmtps in
    case tps of
      [] -> err "can't use amb with no branches (not sure how to type this term)"
      (tp : tps) ->
        foldr (\ tp' me -> me >> ifErr (tp /= tp') "not all branches have same type")
              okay tps >>
        return (TmAmb tms tp)

checkTermh g (UsProd am tms) =
  mapM (checkTerm g) tms >>= return . TmProd am

{-checkTermh g (UsElimAmp tm (o, o')) =
  checkTerm g tm >>= \ (tm, tp) ->
  case tp of
    TpProd am tps ->
      ifErr (am == Multiplicative) "Expected a &-product, not a *-product" >>
      ifErr (not (o' == length tps))
        ("Expected a &-product of arity " ++ show o' ++
          ", but got arity " ++ show (length tps)) >>
      ifErr (not (0 <= o && o < length tps))
        ("expected a number between 0 and " ++ show (length tps)) >>
      return (TmElimAmp tm (o, o') (tps !! o))
    _ -> err "expected ampersand type"
-}

checkTermh g (UsElimProd am tm xs tm') =
  checkTerm g tm >>= \ (tm, tp) ->
  case tp of
    TpProd am' tps ->
      ifErr (am == am') "Mismatched products: * vs &" >>
      ifErr (length tps /= length xs) ("expected " ++ show (length xs) ++ " names, but got " ++ show (length tps)) >>
      let ps = zip xs tps in
        checkTerm (ctxtDeclArgs g ps) tm' >>= \ (tm', tp') ->
        return (TmElimProd tm ps tm' tp')
    _ -> err "expected product type"

checkTermh g (UsEqs tms) =
  mapM (checkTerm g) tms >>= \ tmtps ->
  ifErr (length tmtps == 0) "expected one or more terms to compare with ==" >>
  let (tms, tps) = unzip tmtps in
    foldr (\ tp cr ->
             ifErr (tp /= head tps) "== expects all terms to have the same type" >> cr)
          okay (tail tps) >>
    return (TmEqs tms)
  

-- Check a type under a context
checkType :: Ctxt -> Type -> Either ErrMsg ()

checkType g (TpVar y) =
  mErr (ctxtLookupType g y) ("type variable '" ++ y ++ "' not in scope") >>= \ cs -> okay

checkType g (TpArr tp1 tp2) =
  checkType g tp1 >>
  checkType g tp2

checkType g (TpProd am tps) =
  mapM (checkType g) tps >> okay

checkType g NoTp =
  err "Checking a NoTp"

-- Check and elaborate a case under a context
checkCase :: Ctxt -> Ctor -> CaseUs -> Either ErrMsg (Case, Type)
checkCase g (Ctor x as) (CaseUs x' as' tm) =
  ifErr (x /= x') ("Expected case '" ++ x ++ "' but got '" ++ x' ++ "'") >>
  ifErr (length as /= length as')
    ("Expected " ++ show (length as) ++ " args for case '" ++
      x ++ "', but got " ++ show (length as')) >>
  let g' = ctxtDeclArgs g (zip as' as)
      as'' = zip as' as in
    mapM (\ (a, atp) -> checkAffLin g a atp tm) as'' >>
    checkTerm g' tm >>= \ (tm', tp) ->
    return (Case x as'' tm', tp)

-- Check and elaborate a list of cases under a context
checkCases :: Ctxt -> [Ctor] -> [CaseUs] -> Either ErrMsg ([Case], Type)
checkCases g [] [] = err "Case splitting on empty datatype"
checkCases g (ct : cts) (c : cs) =
  checkCase g ct c >>= \ (c', tp) ->
  checkCasesh g cts cs tp >>= \ cs' ->
  return (c' : cs', tp)
checkCases g _ _ = error "this shouldn't happen"

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
  ifErr (typeIsRecursive g tp') "Start term can't have an infinite domain" >>
  return (Progs [] tm')

checkProgs ds g (UsProgFun x tp tm ps) =
  declErr x (ifBound ds x >> checkType g tp >> checkTerm g tm) >>= \ (tm', tp') ->
  ifErr (tp /= tp')
    ("Expected type of function '" ++ x ++ "' does not match computed type") >>
  checkProgs (x : ds) g ps >>= \ (Progs ps' end) ->
  return (Progs (ProgFun x [] tm' tp : ps') end)

checkProgs ds g (UsProgExtern x tp ps) =
  declErr x (ifBound ds x >>
             checkType g tp >>
             ifErr (typeIsRecursive g tp)
               "external definitions can't have infinite domains") >>
  checkProgs (x : ds) g ps >>= \ (Progs ps' end) ->
  return (Progs (ProgExtern x "0" [] tp : ps') end)

checkProgs ds g (UsProgData x cs ps) =
  declErr x (ifBound ds x >> foldr (\ (Ctor x tps) r -> r >>= \ ds -> ifBound ds x >> foldr (\ tp r -> checkType g tp >> r) okay tps >> return (x : ds)) (return (x : ds)) cs) >>= \ ds' ->
  checkProgs ds' g ps >>= \ (Progs ps' end) ->
  return (Progs (ProgData x cs : ps') end)

-- Check and elaborate a file
checkFile :: UsProgs -> Either String Progs
checkFile ps =
  let bps = progBool ps in
    pickErrHist (checkProgs [] (ctxtDefUsProgs bps) bps)
