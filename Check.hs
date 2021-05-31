module Check where
import Ctxt
import Free


err :: String -> Either String a
err = Left

okay :: Either String ()
okay = Right ()

ifErr :: Bool -> String -> Either String ()
ifErr b e = if b then err e else okay

maybe2 :: Maybe a -> b -> (a -> b) -> b
maybe2 m n j = maybe n j m

checkTerm :: Ctxt -> UsTm -> Either String (Term, Type)
checkTerm g (UsVar x) = maybe2 (ctxtLookupTerm x)
  (err ("Variable '" ++ x ++ "' not in scope"))
  $ \ tp -> return (Var x, tp)
checkTerm g (UsLam x tp tm) =
  err "TODO"
checkTerm g (UsApp tm1 tm2) =
  checkTerm tm1 >>= \ (tm1', tp1) ->
  checkTerm tm2 >>= \ (tm2', tp2) ->
  case tp1 of
    (TpArr tp1a tp1b) ->
      if tp1a == tp2
        then return (TmApp tm1' tm2' tp1a tp1b)
        else err "Application arg types do not match"
    _ -> err "Application to non-arrow type"
checkTerm g (UsCase tm cs) =
  checkTerm g tm >>= \ (tm', tp) ->
  case tp of
    (TpArr _ _) -> err "Case splitting on arrow type"
    (TpVar y) -> maybe2 (ctxtLookupType g y)
      (err "Error in checkTerm UsCase") -- shouldn't happen
      $ \ cs -> err "TODO"
checkTerm g (UsSamp d y) = maybe2 (ctxtLookupType g y)
  (err ("Type variable '" ++ y ++ "' not in scope"))
  $ \ cs ->
    foldr
      (\ (Ctor x as) r -> r >>
        ifErr (not $ null as)
          ("Not sure how to instantiate args for constructor '" ++ x ++ "' when sampling"))
      okay cs >>
    return (TmSamp d y)

checkType :: Ctxt -> Type -> Either String ()
checkType g (TpVar y) = maybe2 (ctxtLookupType g y)
  (err ("Type variable '" ++ y ++ "' not in scope"))
  $ \ cs -> okay
checkType g (TpArr tp1 tp2) =
  checkType g tp1 >>
  checkType g tp2
