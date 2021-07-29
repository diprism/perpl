module RecType where
import qualified Data.Map as Map
import qualified Control.Monad.State.Lazy as State
import Exprs
import Util
import Free
import Ctxt
import Name
import Rename


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
type DisentangleM a = State.State (Map.Map Var DisentangleResult) a
type DisentangleResult = [(Map.Map Var Type, Var, [Case], Type)]

disentangleMake :: Var -> DisentangleResult -> Prog
disentangleMake y ((fvs, name, cs, tp') : []) =
  let as = (targetName, TpVar y) : Map.toList fvs
      rtm = TmCase (TmVarL targetName (TpVar y)) (TpVar y) cs tp' in
    ProgFun name as rtm tp'
disentangleMake y us = error "TODO: Multiple unfolds not implemented yet"

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
      let tp1_us = maybe [] id (Map.lookup (show tp1) unfolds)
          fvs = freeVars' (TmCase (TmVarG DefVar "" [] tp1) tp1 cs' tp2)
          fvs' = Map.toList fvs
          name = unfoldName tp1
          rtm = TmVarG DefVar name ((tm', tp1) : paramsToArgs fvs') tp2 in
        State.put (Map.insert (show tp1) ((fvs, name, cs', tp2) : tp1_us) unfolds) >>
        pure rtm
    | otherwise =
      pure TmCase <*> h tm <*> pure tp1 <*> mapCasesM (const h) cs <*> pure tp2
  h (TmSamp d tp) =
    pure (TmSamp d tp)
  h (TmFold fuf tm tp) =
    pure (TmFold fuf) <*> h tm <*> pure tp

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

--defoldProgs :: [Type] -> Progs -> DefoldM Progs
--defoldProgs = mapProgsM . defoldTerm

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
    (tp, ProgData tname ctors, ProgFun fname [] (joinLams ps tm) (joinArrows (map snd ps) tp))

-- Preprocessing step of defunctionalization
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

{-
defoldAndDisentangle :: Progs -> Either String Progs
defoldAndDisentangle ps =
  disentangleFile ps >>= \ (Progs ps' end', new_ps) ->
  defoldFile (Progs (ps' ++ new_ps) end') >>= \ (Progs ps'' end'', new_ps') ->
  return (Progs (ps'' ++ concat (map (\ (_, p1, p2) -> [p1, p2]) new_ps')) end'')
-}

defunSubst :: Var -> Type -> Type
defunSubst rtp = substType rtp (foldTypeName (TpVar rtp))

drDefun = True
drRefun = False
defunTerm g rtp = derefunTerm drDefun g (rtp, foldTypeName (TpVar rtp)) (applyName (TpVar rtp))
refunTerm g rtp = derefunTerm drRefun g (rtp, unfoldTypeName (TpVar rtp)) (unfoldName (TpVar rtp))

derefunTerm :: Bool -> Ctxt -> (Var, Var) -> Var -> Term -> Term
derefunTerm dr g (rtp, ntp) f = fst . h where

  -- TODO: need to subst inside other datatypes that mention rtp! (Or create new copies?)
  sub = substType rtp ntp

  h_ps :: [Param] -> [Param]
  h_ps = map (fmap sub)
  h_as :: [Arg] -> [Arg]
  h_as = map (h . fst)
  
  h :: Term -> (Term, Type)
  h (TmVarL x tp) = let tp' = sub tp in (TmVarL x tp', tp')
--  h (TmVarG CtorVar x as (TpMaybe tp)) =
--    let tp' = sub tp in (TmVarG CtorVar x (h_as as) (TpMaybe tp'), tp')
  h (TmVarG gv x as tp)
    | dr == drRefun && x == f =
      let ((TmFold False tm _, tp') : fvs) = as in
        -- TODO: sub tp or tp? ---------------------vv (or something else?)
        (joinApps (TmVarL f (joinArrows (map snd as) tp)) ((tm, tp') : fvs), TpVar ntp)
--    | dr == drDefun && x == f =
    | otherwise =
      let tp' = maybe (error ("unknown global var " ++ x)) (\ (_, tp') -> tp')
                (ctxtLookupTerm g x)
          (tps, end) = splitArrows tp'
          tp'' = joinArrows (drop (length as) tps) end in
        (TmVarG gv x (h_as as) tp'', tp'')
  h (TmLam x tp1 tm tp2) =
    let tp1' = sub tp1
        (tm', tp2') = h tm in
      (TmLam x tp1' tm' tp2', TpArr tp1' tp2')
  h (TmApp tm1 tm2 tp2 tp) =
    let (tm1', _) = h tm1
        (tm2', tp2') = h tm2
        tp' = sub tp in
      (TmApp tm1' tm2' tp2' tp', tp')
  h (TmLet x xtm xtp tm tp) =
    let (xtm', xtp') = h xtm
        (tm', tp') = h tm in
    (TmLet x xtm' xtp' tm' tp', tp')
  h (TmCase tm1 tp1 cs tp2) =
    let (tm1', tp1') = h tm1
        cs' = map (\ (Case x ps xtm) -> Case x (h_ps ps) (fst (h xtm))) cs
        tp2' = sub tp2 in
      (TmCase tm1' tp1' cs' tp2', tp2')
  h (TmSamp d tp)
    | isRecType' g rtp [tp] =
      error ("Can't sample from type " ++ show tp ++
              " containing recursive datatype " ++ rtp)
    | otherwise = (TmSamp d tp, tp)
  h (TmFold fuf tm tp)
    | tp == TpVar rtp =
      if dr == drDefun then
        (if fuf then (let (TmVarG DefVar _ [(etm, etp)] _) = tm in h etm) else (TmVarG DefVar f [h tm] (TpVar ntp), TpVar ntp))
      else
        error "TODO"
    | otherwise = let (tm', tp') = h tm in (TmFold fuf tm' tp', tp')



defunProg :: Ctxt -> Var -> Prog -> Prog
defunProg g rtp (ProgFun x ps tm tp)
  | x `elem` [applyName (TpVar rtp), unfoldName (TpVar rtp)] = ProgFun x ps tm tp
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

refun :: Type -> Progs -> Progs
refun tp ps = ps

-- TODO: figure out naming of fold/unfold functions (fold/apply or apply/unfold?)
elimRecTypes :: Progs -> Either String Progs
elimRecTypes ps =
  disentangleFile ps >>= \ (Progs ps' end', new_ps) ->
  defoldFile (Progs (ps' ++ new_ps) end') >>= \ (Progs ps'' end'', new_ps') ->
  let ps3 = Progs (ps'' ++ concat (map (\ (_, p1, p2) -> [p1, p2]) new_ps')) end'' in
    return (retypeProgs (foldr (\ (tp, _, _) -> defun (show tp)) ps3 new_ps'))



retypeTmTp :: Ctxt -> Term -> (Term, Type)
retypeTmTp g tm = let tm' = retypeTerm g tm in (tm', getType tm')

-- TODO: should probably ensure this remains / becomes well-typed
retypeTerm :: Ctxt -> Term -> Term
retypeTerm g (TmVarL x tp) =
  maybe (error ("unknown local var " ++ x)) (TmVarL x . snd) (ctxtLookupTerm g x)
retypeTerm g (TmVarG gv x as tp) =
  let tp' = maybe (error ("unknown global var " ++ x)) (snd . splitArrows . snd) (ctxtLookupTerm g x)
      as' = map (\ (atm, atp) -> retypeTmTp g atm) as in
    TmVarG gv x as' tp'
retypeTerm g (TmLam x tp tm tp') =
  uncurry (TmLam x tp) (retypeTmTp (ctxtDeclTerm g x tp) tm)
retypeTerm g (TmApp tm1 tm2 tp2 tp) =
  case retypeTmTp g tm1 of
    (tm1', TpArr tp2' tp') ->
      TmApp tm1' (retypeTerm g tm2) tp2' tp'
    (tm1', tp12') -> error "Retyping term app where the head is not an arrow type"
retypeTerm g (TmLet x xtm xtp tm tp) =
  let (xtm', xtp') = retypeTmTp g xtm in
    uncurry (TmLet x xtm' xtp') (retypeTmTp (ctxtDeclTerm g x xtp') tm)
retypeTerm g (TmCase tm tp cs tp') =
  -- TODO: tm's synthesized type needs to equal tp
  -- TODO: should tp' stay the same?
  TmCase (retypeTerm g tm) tp (map (\ (Case x ps xtm) -> Case x ps (retypeTerm (ctxtDeclArgs g ps) xtm)) cs) tp'
retypeTerm g (TmSamp d tp) = TmSamp d tp
retypeTerm g (TmFold fuf tm tp) =
  uncurry (TmFold fuf) (retypeTmTp g tm)

retypeProg :: Ctxt -> Prog -> Prog
retypeProg g (ProgFun x ps tm tp) =
  ProgFun x ps (retypeTerm (ctxtDeclArgs g ps) tm) tp
retypeProg g (ProgExtern x xp ps tp) = ProgExtern x xp ps tp
retypeProg g (ProgData y cs) = ProgData y cs

retypeProgs :: Progs -> Progs
retypeProgs ps =
  let g = ctxtDefProgs ps
      Progs ds end = ps in
    Progs (map (retypeProg g) ds) (retypeTerm g end)
