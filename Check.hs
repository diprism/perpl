module Check where
import Ctxt
import Free
import Exprs

err :: String -> Either String a
err = Left

okay :: Either String ()
okay = Right ()

ifErr :: Bool -> String -> Either String ()
ifErr b e = if b then err e else okay

ifBound :: Ctxt -> Var -> Either String ()
ifBound g x = ifErr (ctxtBinds g x) ("'" ++ x ++ "' has multiple definitions")

declErr :: Var -> Either String a -> Either String a
declErr x e = either (\ s -> Left ("In the definition of '" ++ x ++ "': " ++ s)) Right e

maybe2 :: Maybe a -> b -> (a -> b) -> b
maybe2 m n j = maybe n j m

checkTerm :: Ctxt -> UsTm -> Either String (Term, Type)
checkTerm g (UsVar x) = maybe2 (ctxtLookupTerm g x)
  (err ("Variable '" ++ x ++ "' not in scope"))
  $ \ tp -> return (TmVar x tp, tp)
checkTerm g (UsLam x tp tm) =
  ifErr (not $ isAff x tm)
    ("Affine bound variable '" ++ x ++ "' occurs multiple times in the body") >>
  checkTerm (ctxtDeclTerm g x tp) tm >>= \ (tm', tp') ->
  return (TmLam x tp tm' tp', TpArr tp tp')
checkTerm g (UsApp tm1 tm2) =
  checkTerm g tm1 >>= \ (tm1', tp1) ->
  checkTerm g tm2 >>= \ (tm2', tp2) ->
  case tp1 of
    (TpArr tp1a tp1b) ->
      if tp1a == tp2
        then return (TmApp tm1' tm2' tp1a tp1b, tp1b)
        else err "Application arg types do not match"
    _ -> err "Application to non-arrow type"
checkTerm g (UsCase tm cs) =
  checkTerm g tm >>= \ (tm', tp) ->
  case tp of
    (TpArr _ _) -> err "Case splitting on arrow type"
    (TpVar y) -> maybe2 (ctxtLookupType g y)
      (err "Error in checkTerm UsCase") -- shouldn't happen
      $ \ ycs -> checkCases g ycs cs >>= \ (cs', tp') ->
        return (TmCase tm' cs' y tp', tp')
checkTerm g (UsSamp d y) = maybe2 (ctxtLookupType g y)
  (err ("Type variable '" ++ y ++ "' not in scope"))
  $ \ cs ->
    foldr
      (\ (Ctor x as) r -> r >>
        ifErr (not $ null as)
          ("Not sure how to instantiate args for constructor '" ++ x ++ "' when sampling"))
      okay cs >>
    return (TmSamp d y, TpVar y)

checkType :: Ctxt -> Type -> Either String ()
checkType g (TpVar y) = maybe2 (ctxtLookupType g y)
  (err ("Type variable '" ++ y ++ "' not in scope"))
  $ \ cs -> okay
checkType g (TpArr tp1 tp2) =
  checkType g tp1 >>
  checkType g tp2

checkCase :: Ctxt -> Ctor -> CaseUs -> Either String (Case, Type)
checkCase g (Ctor x as) (CaseUs x' as' tm) =
  ifErr (x /= x') ("Expected case '" ++ x ++ "' but got '" ++ x' ++ "'") >>
  ifErr (length as /= length as')
    ("Expected " ++ show (length as) ++ " args for case '" ++
      x ++ "', but got " ++ show (length as')) >>
  let g' = foldr (\ (tp, a) g -> ctxtDeclTerm g a tp) g (zip as as') in
  checkTerm g' tm >>= \ (tm', tp) ->
  return (Case x as' tm', tp)

checkCases :: Ctxt -> [Ctor] -> [CaseUs] -> Either String ([Case], Type)
checkCases g [] [] = err "Case splitting on empty datatype"
checkCases g (ct : cts) (c : cs) =
  checkCase g ct c >>= \ (c', tp) ->
  checkCasesh g cts cs tp >>= \ cs' ->
  return (c' : cs', tp)

checkCasesh :: Ctxt -> [Ctor] -> [CaseUs] -> Type -> Either String [Case]
checkCasesh g [] [] tp = return []
checkCasesh g (ct : cts) (c : cs) tp =
  checkCase g ct c >>= \ (c', tp') ->
  ifErr (tp /= tp') "Cases have different types" >>
  checkCasesh g cts cs tp >>= \ cs' ->
  return (c' : cs')

checkProgs :: Ctxt -> UsProgs -> Either String Progs
checkProgs g (UsProgExec tm) = checkTerm g tm >>= \ (tm', tp') -> return (ProgExec tm')
checkProgs g (UsProgFun x tp tm ps) =
  declErr x (checkTerm g tm) >>= \ (tm', tp') ->
  ifErr (tp /= tp')
    ("Expected type of function '" ++ x ++ "' does not match computed type") >>
  checkProgs g ps >>= \ ps' ->
  return (ProgFun x tp tm' ps')
checkProgs g (UsProgData x cs ps) =
  declErr x (foldr (\ (Ctor x tps) r -> foldr (\ tp r -> checkType g tp >> r) okay tps >> r) okay cs) >>
  checkProgs g ps >>= \ ps' ->
  return (ProgData x cs ps')

declProgs :: Ctxt -> UsProgs -> Either String Ctxt
declProgs g (UsProgExec tm) = return g
declProgs g (UsProgFun x tp tm ps) =
  ifBound g x >>
  declProgs (ctxtDeclTerm g x tp) ps
declProgs g (UsProgData y cs ps) =
  ifBound g y >>
  foldl (\ r (Ctor x tps) -> r >>= \ g' -> ifBound g' x >> return (ctxtDeclTerm g' x (TpVar ""))) (return $ ctxtDeclType g y []) cs >>
  declProgs (ctxtDeclType g y cs) ps

checkFile :: UsProgs -> Either String Progs
checkFile ps = declProgs emptyCtxt ps >>= \ g' -> checkProgs g' ps
