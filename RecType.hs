module RecType where
import qualified Data.Map as Map
import qualified Control.Monad.State.Lazy as State
import Exprs
import Util
import Free
import Ctxt
import Name


isRecType' :: Ctxt -> Var -> [Type] -> Bool
isRecType' g y = h [] where
  h :: [Var] -> [Type] -> Bool
  h hist [] = False
  h hist (TpArr tp1 tp2 : tps) = h hist (tp1 : tp2 : tps)
  h hist (TpVar y' : tps)
    | y == y' = True
    | y' `elem` hist = h hist tps
    | otherwise = maybe
      (h hist tps)
      (\ cs -> h (y' : hist) (foldr (\ (Ctor x as) tps -> as ++ tps) tps cs))
      (ctxtLookupType g y')
  h hist (TpMaybe tp : tps) = h hist (tp : tps)
  h hist (TpBool : tps) = h hist tps

isRecDatatype :: Ctxt -> Var -> Bool
isRecDatatype g y =
  maybe False (isRecType' g y . concat . map (\ (Ctor _ tp) -> tp)) (ctxtLookupType g y)

isRecType :: Ctxt -> Type -> Bool
isRecType g (TpVar y) = isRecDatatype g y
isRecType g _ = False

getRecTypes' :: Ctxt -> [Prog] -> [Var]
getRecTypes' g (ProgData y cs : ds) =
  if isRecDatatype g y then y : getRecTypes' g ds else getRecTypes' g ds
getRecTypes' g (ProgFun x ps tm tp : ds) = getRecTypes' g ds
getRecTypes' g (ProgExtern x xp ps tp : ds) = getRecTypes' g ds
getRecTypes' g [] = []

getRecTypes :: Progs -> [Type]
getRecTypes (Progs ds end) =
  map TpVar (getRecTypes' (ctxtDefProgs (Progs ds end)) ds)


-- N.B. state list is in reverse order
type DisentangleM a = State.State [DisentangleResult] a
type DisentangleResult = (Map.Map Var Type, Var, Type, [Case], Type)

disentangleMake :: Int -> DisentangleResult -> Prog
disentangleMake i (fvs, name, tp, cs, tp') =
  let as = (targetName, tp) : Map.toList fvs
      rtm = TmCase (TmVarL targetName tp) tp cs tp' in
    ProgFun name as rtm tp

-- See `disentangleFile`
disentangleTerm :: [Type] -> Term -> DisentangleM Term
disentangleTerm recs = h where
  h :: Term -> DisentangleM Term
  h (TmVarL x tp) = pure (TmVarL x tp)
  h (TmVarG gv x as tp) =
    pure (TmVarG gv x) <*> mapArgsM h as <*> pure tp
  h (TmLam x tp tm tp') =
    pure (TmLam x tp) <*> h tm <*> pure tp'
  h (TmApp tm1 tm2 tp2 tp) =
    pure TmApp <*> h tm1 <*> h tm2 <*> pure tp2 <*> pure tp
  h (TmLet x xtm xtp tm tp) =
    pure (TmLet x) <*> h xtm <*> pure xtp <*> h tm <*> pure tp
  h (TmCase tm tp1 cs tp2)
    | tp1 `elem` recs =
      h tm >>= \ tm' ->
      mapCasesM (const h) cs >>= \ cs' ->
      State.get >>= \ unfolds ->
      let fvs = freeVars' (TmCase (TmVarG DefVar "" [] tp1) tp1 cs' tp2)
          fvs' = Map.toList fvs
          name = unfoldName (length unfolds)
          rtm = TmVarG DefVar name ((tm', tp1) : paramsToArgs fvs') tp2 in
        State.put ((fvs, name, tp1, cs', tp2) : unfolds) >>
        pure rtm
    | otherwise =
      pure TmCase <*> h tm <*> pure tp1 <*> mapCasesM (const h) cs <*> pure tp2
  h (TmSamp d tp) =
    pure (TmSamp d tp)
  h (TmFold fuf tm tp) =
    pure (TmFold fuf) <*> h tm <*> pure tp

-- Abstracts each unfold of a recursive datatype to its own function
disentangleFile :: Progs -> Either String (Progs, [Prog])
disentangleFile ps =
  let recs = getRecTypes ps
      dm = mapProgsM (disentangleTerm recs) ps
      mkProgs = map (uncurry disentangleMake) . enumerate . reverse in
  return $ fmap mkProgs $ State.runState dm []



type DefoldM a = State.State (Map.Map Var [Term]) a

defoldTerm :: [Type] -> Term -> DefoldM Term
defoldTerm recs = h where
  h :: Term -> DefoldM Term
  h (TmVarL x tp) = pure (TmVarL x tp)
  h (TmVarG gv x as tp) = pure (TmVarG gv x) <*> mapArgsM h as <*> pure tp
  h (TmLam x tp tm tp') = pure (TmLam x tp) <*> h tm <*> pure tp'
  h (TmApp tm1 tm2 tp2 tp) = pure TmApp <*> h tm1 <*> h tm2 <*> pure tp2 <*> pure tp
  h (TmLet x xtm xtp tm tp) = pure (TmLet x) <*> h xtm <*> pure xtp <*> h tm <*> pure tp
  h (TmCase tm tp1 cs tp2) = pure TmCase <*> h tm <*> pure tp1 <*> mapCasesM (const h) cs <*> pure tp2
  h (TmSamp d tp) = pure (TmSamp d tp) -- TODO: anything here?
  h (TmFold fuf tm tp)
    | fuf && tp `elem` recs =
      h tm >>= \ tm' ->
      State.get >>= \ fs ->
      let fvs = Map.toList (freeVars' tm')
          cname = foldCtorName tp (maybe 0 length (Map.lookup (show tp) fs))
          tname = foldTypeName tp
          aname = applyName tp
          fld = TmVarG CtorVar cname (paramsToArgs fvs) (TpVar tname)
      in
        State.put (Map.insertWith (\ new old -> old ++ new) (show tp) [tm'] fs) >>
        return (TmFold fuf (TmVarG DefVar aname [(fld, TpVar tname)] tp) tp)
    | otherwise = pure (TmFold fuf) <*> h tm <*> pure tp

defoldProgs :: [Type] -> Progs -> DefoldM Progs
defoldProgs = mapProgsM . defoldTerm

makeDefold :: Type -> [Term] -> (Type, Prog, Prog)
makeDefold tp tms =
  let fname = applyName tp
      tname = foldTypeName tp
      ftp = TpVar tname
      ps = [(targetName, ftp)]
      casesf = \ (i, tm) -> Case (foldCtorName tp i) (Map.toList (freeVars' tm)) tm
      cases = map casesf (enumerate tms)
      ctors = map (\ (Case x ps tm) -> Ctor x (map snd ps)) cases
      tm = TmCase (TmVarL targetName ftp) ftp cases tp
  in
    (tp, ProgData tname ctors, ProgFun fname ps tm tp)

-- Abstracts the folds for each recursive datatype into an apply function for each datatype
-- returns (modified progs, (OrigTp, data Fold = ..., apply : Fold -> OrigTp = ...))
defoldFile :: Progs -> Either String (Progs, [(Type, Prog, Prog)])
defoldFile ps =
  let recs = getRecTypes ps
      dm = mapProgsM (defoldTerm recs) ps
      (ps', fs) = State.runState dm Map.empty
      fs' = map (\ tp -> Map.lookup (show tp) fs >>= Just . makeDefold tp) recs
      new_ps = foldr (maybe id (:)) [] fs'
  in
    return (ps', new_ps)

defoldAndDisentangle :: Progs -> Either String Progs
defoldAndDisentangle ps =
  disentangleFile ps >>= \ (Progs ps' end', new_ps) ->
  defoldFile (Progs (ps' ++ new_ps) end') >>= \ (Progs ps'' end'', new_ps') ->
  return (Progs (ps'' ++ concat (map (\ (_, p1, p2) -> [p1, p2]) new_ps')) end'')

defunctionalize :: Type -> Progs -> Progs
defunctionalize tp ps = ps

refunctionalize :: Type -> Progs -> Progs
refunctionalize tp ps = ps

elimRecTypes :: Progs -> Either String Progs
elimRecTypes ps = return ps
