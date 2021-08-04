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
type DisentangleResult = [(Map.Map Var Type, [Case], Type)]

disentangleMake :: Ctxt -> Var -> DisentangleResult -> (Prog, Prog)
{-disentangleMake g y ((fvs, name, cs, tp') : []) =
  let utpn = unfoldTypeName y
      uctn = unfoldCtorName y
      ps' = Map.toList fvs
      ps = (targetName, TpVar y) : ps'
--      rtm = TmCase (TmVarL targetName (TpVar y)) (TpVar y) cs tp'
      arrtp = joinArrows (map snd ps') tp'
      csf = \ (Case x xps xtm) -> Case x xps $ TmVarG CtorVar uctn [(joinLams ps' xtm, arrtp)] (TpVar utpn)
      rtm = TmCase (TmVarL targetName (TpVar y)) (TpVar y) (map csf cs) (TpVar utpn)

--      fun = ProgFun name [] (joinLams ps rtm) (joinArrows (map snd ps) tp')
      fun = ProgFun name [] (TmLam targetName (TpVar y) rtm (TpVar utpn)) (TpArr (TpVar y) (TpVar utpn))
      dat = ProgData utpn [Ctor uctn [arrtp]] in
    (fun, dat)
-}
disentangleMake g y ((fvs, cs, tp') : []) =
  let utpn = unfoldTypeName y
      uctn = unfoldCtorName y
      ps' = Map.toList fvs
      sub_ps = \ (x, tp) -> (x, derefunSubst Refun y tp)
      ps = (targetName, TpVar y) : map sub_ps ps'
      arrtp = joinArrows (map snd ps') tp'
      csf = \ (Case x xps xtm) -> Case x (map sub_ps xps) $ TmVarG CtorVar uctn [(joinLams ps' (derefunTerm Refun (ctxtDeclArgs g (xps ++ (targetName, TpVar y) : ps')) y xtm), arrtp)] (TpVar utpn)
      rtm = TmCase (TmVarL targetName (TpVar y)) (TpVar y) (map csf cs) (TpVar utpn)
      fun = ProgFun (unfoldName y) [] (TmLam targetName (TpVar y) rtm (TpVar utpn)) (TpArr (TpVar y) (TpVar utpn))
      dat = ProgData utpn [Ctor uctn [arrtp]] in
    (dat, fun)
disentangleMake g y (u : us) = error "TODO: Multiple unfolds not implemented yet"

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
      -- TODO: here we use length unfolds and use the ctor for that number
      let TpVar y = tp1
          y_us = maybe [] id (Map.lookup y unfolds)
          fvs = freeVars' (TmCase (TmVarG DefVar "" [] (TpVar y)) (TpVar y) cs' tp2)
          fvs' = Map.toList fvs
          tparr = joinArrows (map snd fvs') tp2
          x' = targetName -- TODO: pick better name?
          rtm = TmCase tm (TpVar (unfoldTypeName y)) [Case (unfoldCtorName y) [(x', tparr)] (joinApps (TmVarL x' tparr) (paramsToArgs fvs'))] tp2
      in
        State.put (Map.insert y ((fvs, cs', tp2) : y_us) unfolds) >>
        pure rtm
{-    | tp1 `elemRecs` recs =
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
        pure rtm-}
    | otherwise =
      pure TmCase <*> h tm <*> pure tp1 <*> mapCasesM (const h) cs <*> pure tp2
  h (TmSamp d tp) =
    pure (TmSamp d tp)

-- Preprocessing step of refunctionalization
-- Abstracts each unfold of a recursive datatype to its own function
disentangleFile :: Progs -> Either String (Progs, [(Var, Prog, Prog)])
disentangleFile ps =
  let recs = getRecTypes ps
      dm = mapProgsM (disentangleTerm recs) ps
      (ps', us) = State.runState dm Map.empty
      ps'' = foldr (derefunProgsTypes Refun) ps' recs
      g = ctxtDefProgs ps''
      mkProgs = \ (x, u) -> let (fun, dat) = disentangleMake g x (reverse u) in (x, fun, dat)
      us' = map mkProgs (Map.toList us)
  in
  return (ps'', us')

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

makeDefold :: Ctxt  -> Var -> [Term] -> (Var, Prog, Prog)
makeDefold g y tms =
  let fname = applyName y
      tname = foldTypeName y
      ftp = TpVar tname
      ps = [(targetName, ftp)]
      casesf = \ (i, tm) -> let ps' = Map.toList (freeVars' tm) in Case (foldCtorName y i) ps' (derefunTerm Defun (ctxtDeclArgs g ps') y tm)
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
      ps'' = foldr (derefunProgsTypes Defun) ps' recs
      g = ctxtDefProgs ps''
      fs' = map (\ y -> Map.lookup y fs >>= Just . makeDefold g y) recs
      new_ps = foldr (maybe id (:)) [] fs'
  in
    return (ps'', new_ps)

data DeRe = Defun | Refun
  deriving Eq

derefunSubst :: DeRe -> Var -> Type -> Type
derefunSubst dr rtp = substType rtp (if dr == Defun then foldTypeName rtp else unfoldTypeName rtp)

defunTerm = derefunTerm Defun
refunTerm = derefunTerm Refun

derefunTerm :: DeRe -> Ctxt -> Var -> Term -> Term
derefunTerm dr g rtp = fst . h where

  foldTypeN = foldTypeName rtp
  applyN = applyName rtp
  unfoldN = unfoldName rtp
  unfoldTypeN = unfoldTypeName rtp
  
  sub = substType rtp (if dr == Defun then foldTypeN else unfoldTypeN)

  h_ps :: [Param] -> [Param]
  h_ps = map (fmap sub)
  h_as :: [Arg] -> [Arg]
  h_as = map (h . fst)
  
  h :: Term -> (Term, Type)
  h (TmVarL x tp) = let tp' = sub tp in (TmVarL x tp', tp')
  h (TmVarG gv x as tp)
{-    | dr == Refun && gv == DefVar && x == unfoldN =
      let ((ctm, ctp) : as') = h_as as
          x' = targetName
          arrtp = joinArrows (map snd as') tp
          (ptm, ptp) = h (joinApps (TmVarL x' arrtp) as')
      in
        (TmCase ctm ctp [Case (unfoldCtorName rtp) [(x', arrtp)] ptm] ptp, ptp)-}
    | dr == Refun && gv == CtorVar && tp == TpVar rtp =
      (TmVarG DefVar unfoldN [(TmVarG gv x (h_as as) tp, tp)] (TpVar unfoldTypeN), TpVar unfoldTypeN)
    | dr == Defun && gv == DefVar && x == applyN =
      let [(etm, etp)] = as in h etm
    | otherwise =
      let tp' = maybe (error ("unknown global var " ++ x)) (\ (_, tp') -> tp')
                  (ctxtLookupTerm g x)
          (tps, end) = splitArrows tp'
          tp'' = joinArrows (drop (length as) tps) end in
--          tp'' = joinArrows (map sub (drop (length as) tps)) (if gv == CtorVar then end else sub end) in
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
    | dr == Defun && tp1 == TpVar rtp =
        let (tm1', tp1') = h tm1
            cs' = map (\ (Case x ps xtm) -> Case x (h_ps ps) (fst (h xtm))) cs
            tp2' = case cs' of [] -> sub tp2; (Case x ps xtm : _) -> getType xtm in
          (TmCase (TmVarG DefVar applyN [(tm1', tp1')] (TpVar rtp)) (TpVar rtp) cs' tp2', tp2')
{-    | dr == Refun && tp1 == TpVar rtp =
        let (tm1', tp1') = h tm1
            cs' = map (\ (Case x ps xtm) -> Case x (h_ps ps) (fst (h xtm))) cs
            tp2' = case cs' of [] -> sub tp2; (Case x ps xtm : _) -> getType xtm in
          (TmCase tm1' tp1' cs' tp2', tp2') -} -- Same as otherwise
    | otherwise =
        let (tm1', tp1') = h tm1
            cs' = map (\ (Case x ps xtm) -> Case x (h_ps ps) (fst (h xtm))) cs
            tp2' = case cs' of [] -> sub tp2; (Case x ps xtm : _) -> getType xtm in
          (TmCase tm1' tp1' cs' tp2', tp2')
  h (TmSamp d tp) = (TmSamp d tp, tp)


derefunProgTypes :: DeRe -> Var -> Prog -> Prog
derefunProgTypes dr rtp (ProgFun x ps tm tp)
--  | (dr == Defun && x == applyName rtp) || (dr == Refun && x == unfoldName rtp) = ProgFun x ps tm tp
  | otherwise = ProgFun x (map (fmap (derefunSubst dr rtp)) ps) tm (derefunSubst dr rtp tp)
derefunProgTypes dr rtp (ProgExtern x xp ps tp) = ProgExtern x xp ps tp
derefunProgTypes dr rtp (ProgData y cs) = ProgData y (map (\ (Ctor x tps) -> Ctor x (map (derefunSubst dr rtp) tps)) cs)

derefunProgsTypes :: DeRe -> Var -> Progs -> Progs
derefunProgsTypes dr rtp (Progs ps end) =
  Progs (map (derefunProgTypes dr rtp) ps) end

derefunProg' :: DeRe -> Ctxt -> Var -> Prog -> Prog
derefunProg' dr g rtp (ProgFun x ps tm tp)
{-  | (dr == Defun && x == applyName rtp) =
    let tm' = derefunTerm dr g rtp tm in
      ProgFun x ps tm' tp
  | (dr == Refun && x == unfoldName rtp) =
    let tm' = tm in -- TODO?
      ProgFun x ps tm' tp-}
  | otherwise = ProgFun x
--      (map (fmap (derefunSubst dr rtp)) ps)
      ps
      (derefunTerm dr g rtp tm)
      tp
--      (derefunSubst dr rtp tp)
derefunProg' dr g rtp (ProgExtern x xp ps tp) = ProgExtern x xp ps tp
derefunProg' dr g rtp (ProgData y cs)
--  | y == rtp = ProgData y (map (\ (Ctor x tps) -> Ctor x (map (derefunSubst dr rtp) tps)) cs) -- anyways, we'd need to substitute in this to change things that reference String to %UnfoldString% or whatever
  | otherwise = ProgData y cs

derefun :: DeRe -> Var -> [Prog] -> Progs -> Progs
derefun dr rtp new_ps (Progs ps end) =
  let --g = ctxtDefProgs (Progs (ps ++ new_ps) end)
      g = ctxtDefProgs (Progs (ps ++ new_ps) end)
      ps' = Progs (map (derefunProg' dr g rtp) ps) (derefunTerm dr g rtp end)
  in
    ps'

defun :: Var -> [Prog] -> Progs -> Progs
defun = derefun Defun

refun :: Var -> [Prog] -> Progs -> Progs
refun = derefun Refun

insertProgs' :: [Prog] -> [(Var, (Prog, Prog))] -> [Prog]
insertProgs' [] new_ds = []
insertProgs' (ProgData y cs : ds) new_ds = maybe [ProgData y cs] (\ (p1, p2) -> [ProgData y cs, p1, p2]) (lookup y new_ds) ++ (insertProgs' ds new_ds)
insertProgs' (d : ds) new_ds = d : insertProgs' ds new_ds

insertProgs :: Progs -> [(Var, Prog, Prog)] -> Progs
insertProgs (Progs ds end) new_ps = Progs (insertProgs' ds (map (\ (x, p1, p2) -> (x, (p1, p2))) new_ps)) end

-- TODO: figure out naming of fold/unfold functions (fold/apply or apply/unfold?)
elimRecTypes :: Progs -> Either String Progs
elimRecTypes ps =
  let dr = Refun in
    (if dr == Defun then defoldFile else disentangleFile) ps >>= \ (ps', new_ps) ->
    let new_ps' = concat (map (\ (_, p1, p2) -> [p1, p2]) new_ps) in
      return (insertProgs (foldr (\ (tp, _, _) -> derefun dr tp new_ps') ps' new_ps) new_ps)

{-  -- Only necessary when refunctionalizing
  disentangleFile ps >>= \ (Progs ps' end', new_ps) ->
  -- Only necessary when defunctionalizing
  defoldFile (Progs (ps' ++ new_ps) end') >>= \ (Progs ps'' end'', new_ps') ->
  let ps3 = Progs (ps'' ++ concat (map (\ (_, p1, p2) -> [p1, p2]) new_ps')) end'' in
    return (foldr (\ (tp, _, _) -> refun tp) ps3 new_ps')
-}
