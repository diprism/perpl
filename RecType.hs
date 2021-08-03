module RecType where
import qualified Data.Map as Map
import qualified Control.Monad.State.Lazy as State
import Exprs
import Util
import Free
import Ctxt
import Name
import Rename
import Show

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

getRecTypes :: Progs -> [Var]
getRecTypes (Progs ds end) =
  getRecTypes' (ctxtDefProgs (Progs ds end)) ds

elemRecs :: Type -> [Var] -> Bool
elemRecs (TpVar y) recs = y `elem` recs
elemRecs _ _ = False


-- N.B. state list is in reverse order
type DisentangleM a = State.State (Map.Map Var DisentangleResult) a
type DisentangleResult = [(Map.Map Var Type, Var, [Case], Type)]

disentangleMake :: Var -> DisentangleResult -> Prog
disentangleMake y ((fvs, name, cs, tp') : []) =
  let ps = (targetName, TpVar y) : Map.toList fvs
      rtm = TmCase (TmVarL targetName (TpVar y)) (TpVar y) cs tp' in
    ProgFun name [] (joinLams ps rtm) (joinArrows (map snd ps) tp')
disentangleMake y us = error "TODO: Multiple unfolds not implemented yet"

-- See `disentangleFile`
disentangleTerm :: [Var] -> Term -> DisentangleM Term
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
    | tp1 `elemRecs` recs =
      h tm >>= \ tm' ->
      mapCasesM (const h) cs >>= \ cs' ->
      State.get >>= \ unfolds ->
      let TpVar y = tp1
          y_us = maybe [] id (Map.lookup y unfolds)
          fvs = freeVars' (TmCase (TmVarG DefVar "" [] (TpVar y)) (TpVar y) cs' tp2)
          fvs' = Map.toList fvs
          name = unfoldName y
          rtm = TmVarG DefVar name ((tm', TpVar y) : paramsToArgs fvs') tp2 in
        State.put (Map.insert y ((fvs, name, cs', tp2) : y_us) unfolds) >>
        pure rtm
    | otherwise =
      pure TmCase <*> h tm <*> pure tp1 <*> mapCasesM (const h) cs <*> pure tp2
  h (TmSamp d tp) =
    pure (TmSamp d tp)

-- Preprocessing step of refunctionalization
-- Abstracts each unfold of a recursive datatype to its own function
disentangleFile :: Progs -> Either String (Progs, [Prog])
disentangleFile ps =
  let recs = getRecTypes ps
      dm = mapProgsM (disentangleTerm recs) ps
      mkProgs = \ (x, u) -> disentangleMake x (reverse u)
      (ps', us) = State.runState dm Map.empty
      us' = map mkProgs (Map.toList us)
  in
  return (ps', us')

type DefoldM a = State.State (Map.Map Var [Term]) a

defoldTerm :: [Var] -> Term -> DefoldM Term
defoldTerm recs = h where
  h :: Term -> DefoldM Term
  h (TmVarL x tp) = pure (TmVarL x tp)
  h (TmVarG gv x as tp)
    | gv == CtorVar && tp `elemRecs` recs =
        mapArgsM h as >>= \ as' ->
        State.get >>= \ fs ->
        let TpVar y = tp
            fvs = Map.toList (freeVarsArgs' as')
            cname = foldCtorName y (maybe 0 length (Map.lookup y fs))
            tname = foldTypeName y
            aname = applyName y
            fld = TmVarG CtorVar cname (paramsToArgs fvs) (TpVar tname)
        in
          State.put (Map.insertWith (flip (++)) y [TmVarG CtorVar x as' (TpVar y)] fs) >>
          return (TmVarG DefVar aname [(fld, TpVar tname)] (TpVar y))
    | otherwise = pure (TmVarG gv x) <*> mapArgsM h as <*> pure tp
  h (TmLam x tp tm tp') = pure (TmLam x tp) <*> h tm <*> pure tp'
  h (TmApp tm1 tm2 tp2 tp) = pure TmApp <*> h tm1 <*> h tm2 <*> pure tp2 <*> pure tp
  h (TmLet x xtm xtp tm tp) = pure (TmLet x) <*> h xtm <*> pure xtp <*> h tm <*> pure tp
  h (TmCase tm tp1 cs tp2) = pure TmCase <*> h tm <*> pure tp1 <*> mapCasesM (const h) cs <*> pure tp2
  h (TmSamp d tp) = pure (TmSamp d tp)

makeDefold :: Var -> [Term] -> (Var, Prog, Prog)
makeDefold y tms =
  let fname = applyName y
      tname = foldTypeName y
      ftp = TpVar tname
      ps = [(targetName, ftp)]
      casesf = \ (i, tm) -> Case (foldCtorName y i) (Map.toList (freeVars' tm)) tm
      cases = map casesf (enumerate tms)
      ctors = map (\ (Case x ps tm) -> Ctor x (map snd ps)) cases
      tm = TmCase (TmVarL targetName ftp) ftp cases (TpVar y)
  in
    (y, ProgData tname ctors, ProgFun fname [] (joinLams ps tm) (joinArrows (map snd ps) (TpVar y)))

-- Preprocessing step of defunctionalization
-- Abstracts the folds for each recursive datatype into an apply function for each datatype
-- returns (modified progs, (OrigTp, data Fold = ..., apply : Fold -> OrigTp = ...))
defoldFile :: Progs -> Either String (Progs, [(Var, Prog, Prog)])
defoldFile ps =
  let recs = getRecTypes ps
      dm = mapProgsM (defoldTerm recs) ps
      (ps', fs) = State.runState dm Map.empty
      fs' = map (\ y -> Map.lookup y fs >>= Just . makeDefold y) recs
      new_ps = foldr (maybe id (:)) [] fs'
  in
    return (ps', new_ps)

{-
defoldAndDisentangle :: Progs -> Either String Progs
defoldAndDisentangle ps =
  disentangleFile ps >>= \ (Progs ps' end', new_ps) ->
  defoldFile (Progs (ps' ++ new_ps) end') >>= \ (Progs ps'' end'', new_ps') ->
  return (Progs (ps'' ++ concat (map (\ (_, p1, p2) -> [p1, p2]) new_ps')) end'')
-}

defunSubst :: Var -> Type -> Type
defunSubst rtp = substType rtp (foldTypeName rtp)

drDefun = True
drRefun = False
defunTerm g rtp = derefunTerm drDefun g (rtp, foldTypeName rtp) -- (applyName rtp)
refunTerm g rtp = derefunTerm drRefun g (rtp, unfoldTypeName rtp) -- (unfoldName rtp)

derefunTerm :: Bool -> Ctxt -> (Var, Var) -> Term -> Term
derefunTerm dr g (rtp, ntp) = fst . h where

  foldTypeN = foldTypeName rtp
  applyN = applyName rtp
  unfoldN = unfoldName rtp
  unfoldTypeN = unfoldTypeN
  
  sub = substType rtp ntp

  h_ps :: [Param] -> [Param]
  h_ps = map (fmap sub)
  h_as :: [Arg] -> [Arg]
  h_as = map (h . fst)
  
  h :: Term -> (Term, Type)
  h (TmVarL x tp) = let tp' = sub tp in (TmVarL x tp', tp')
  h (TmVarG gv x as tp)
    | dr == drRefun && gv == DefVar && x == unfoldN =
        error "TODO"
    | dr == drDefun && gv == DefVar && x == applyN =
        let [(etm, etp)] = as in h etm
    | otherwise =
      let tp' = maybe (error ("unknown global var " ++ x)) (\ (_, tp') -> tp')
                  (ctxtLookupTerm g x)
          (tps, end) = splitArrows tp'
          tp'' = joinArrows (map sub (drop (length as) tps)) (if gv == CtorVar then end else sub end) in
        (TmVarG gv x (h_as as) tp'', tp'')
  h (TmLam x tp1 tm tp2) =
    let tp1' = sub tp1
        (tm', tp2') = h tm in
      (TmLam x tp1' tm' tp2', TpArr tp1' tp2')
  h (TmApp tm1 tm2 tp2 tp) =
    let (tm1', TpArr _ tp') = h tm1
        (tm2', tp2') = h tm2 in
      (TmApp tm1' tm2' tp2' tp', tp')
  h (TmLet x xtm xtp tm tp) =
    let (xtm', xtp') = h xtm
        (tm', tp') = h tm in
    (TmLet x xtm' xtp' tm' tp', tp')
  h (TmCase tm1 tp1 cs tp2)
    | dr == drDefun && tp1 == TpVar rtp =
        let (tm1', tp1') = h tm1
            cs' = map (\ (Case x ps xtm) -> Case x (h_ps ps) (fst (h xtm))) cs
            tp2' = case cs' of [] -> sub tp2; (Case x ps xtm : _) -> getType xtm in
          (TmCase (TmVarG DefVar applyN [(tm1', tp1')] (TpVar rtp)) (TpVar rtp) cs' tp2', tp2')
    | otherwise =
        let (tm1', tp1') = h tm1
            cs' = map (\ (Case x ps xtm) -> Case x (h_ps ps) (fst (h xtm))) cs
            tp2' = case cs' of [] -> sub tp2; (Case x ps xtm : _) -> getType xtm in
          (TmCase tm1' tp1' cs' tp2', tp2')
  h (TmSamp d tp) = (TmSamp d tp, tp)


defunProg :: Ctxt -> Var -> Prog -> Prog
defunProg g rtp (ProgFun x ps tm tp)
  | x == applyName rtp = ProgFun x ps tm tp
  | otherwise = ProgFun x (map (fmap (defunSubst rtp)) ps) tm (defunSubst rtp tp)
defunProg g rtp (ProgExtern x xp ps tp)
  | isRecType' g rtp (tp : ps) = error "Extern defs can't use recursive datatypes"
  | otherwise = ProgExtern x xp ps tp
defunProg g rtp (ProgData y cs)
  | y == rtp = ProgData y (map (\ (Ctor x tps) -> Ctor x (map (defunSubst rtp) tps)) cs)
  | otherwise = ProgData y cs

defun :: Var -> Progs -> Progs
defun rtp (Progs ps end) =
  let g = ctxtDefProgs (Progs ps end)
      ps' = Progs (map (defunProg g rtp) ps) end
      g' = ctxtDefProgs ps'
      Just ps'' = mapProgsM (Just . defunTerm g rtp) ps'
  in
    ps''

refun :: Var -> Progs -> Progs
refun rtp ps = ps

-- TODO: figure out naming of fold/unfold functions (fold/apply or apply/unfold?)
elimRecTypes :: Progs -> Either String Progs
elimRecTypes ps =
  disentangleFile ps >>= \ (Progs ps' end', new_ps) ->
  defoldFile (Progs (ps' ++ new_ps) end') >>= \ (Progs ps'' end'', new_ps') ->
  let ps3 = Progs (ps'' ++ concat (map (\ (_, p1, p2) -> [p1, p2]) new_ps')) end'' in
    --Left (showProgsV (foldr (\ (tp, _, _) -> defun tp) ps3 new_ps'))
    return (foldr (\ (tp, _, _) -> defun tp) ps3 new_ps')
