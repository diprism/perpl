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
  maybe False (isRecType' g y . concatMap (\ (Ctor _ tps) -> tps)) (ctxtLookupType g y)

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

type DisentangleM a = State.State [[Case]] a

collectUnfolds :: Var -> Term -> [(FreeVars, Type)]
collectUnfolds rtp (TmVarL x tp) = []
collectUnfolds rtp (TmVarG gv x as tp) = concatMap (\ (atm, atp) -> collectUnfolds rtp atm) as
collectUnfolds rtp (TmLam x tp tm tp') = collectUnfolds rtp tm
collectUnfolds rtp (TmApp tm1 tm2 tp2 tp) = collectUnfolds rtp tm1 ++ collectUnfolds rtp tm2
collectUnfolds rtp (TmLet x xtm xtp tm tp) = collectUnfolds rtp xtm ++ collectUnfolds rtp tm
collectUnfolds rtp (TmCase tm tp1 cs tp2) =
  let fvs = freeVarsCases' cs
      this = if tp1 == TpVar rtp then [(fvs, tp2)] else [] in
    collectUnfolds rtp tm
      ++ concatMap (\ (Case cx cps ctm) -> collectUnfolds rtp ctm) cs
      ++ this
collectUnfolds rtp (TmSamp d tp) = []
collectUnfolds rtp (TmAmb tms tp) = concatMap (collectUnfolds rtp) tms

collectFolds :: Var -> Term -> [(Var, FreeVars)]
collectFolds rtp (TmVarL x tp) = []
collectFolds rtp (TmVarG gv x as tp) =
  let this = if TpVar rtp == tp then [(x, freeVarsArgs' as)] else [] in
    concatMap (\ (atm, atp) -> collectFolds rtp atm) as ++ this
collectFolds rtp (TmLam x tp tm tp') = collectFolds rtp tm
collectFolds rtp (TmApp tm1 tm2 tp2 tp) = collectFolds rtp tm1 ++ collectFolds rtp tm2
collectFolds rtp (TmLet x xtm xtp tm tp) = collectFolds rtp xtm ++ collectFolds rtp tm
collectFolds rtp (TmCase tm tp cs tp') = collectFolds rtp tm ++ concatMap (\ (Case cx cps ctm) -> collectFolds rtp ctm) cs
collectFolds rtp (TmSamp d tp) = []
collectFolds rtp (TmAmb tms tp) = concatMap (collectFolds rtp) tms

collectProg :: (Term -> [a]) -> Prog -> [a]
collectProg f (ProgFun _ _ tm _) = f tm
collectProg f _ = []

collectFile :: (Term -> [a]) -> Progs -> [a]
collectFile f (Progs ps end) = concatMap (collectProg f) ps ++ f end

collectUnfoldsFile = collectFile . collectUnfolds
collectFoldsFile = collectFile . collectFolds


makeUnfoldDatatype :: Var -> [(FreeVars, Type)] -> Prog
makeUnfoldDatatype y = ProgData (unfoldTypeName y) . map (\ (i, (fvs, tp)) -> Ctor (unfoldCtorName y i) [joinArrows (Map.elems fvs) tp]) . enumerate

makeFoldDatatype :: Var -> [(Var, FreeVars)] -> Prog
makeFoldDatatype y = ProgData (foldTypeName y) . map (\ (i, (x, fvs)) -> Ctor (foldCtorName y i) (map snd (Map.toList fvs))) . enumerate

ambAll :: [Term] -> Type -> Term
ambAll [] tp = TmSamp DistFail tp
ambAll [tm] tp = tm
ambAll tms tp = TmAmb tms tp
--ambAll (tm : tms) tp = tmIf (TmSamp DistAmb TpBool) (ambAll tms tp) tm tp

makeDisentangle :: Ctxt -> Var -> [(FreeVars, Type)] -> [[Case]] -> (Prog, Prog)
makeDisentangle g y us css =
  let ytp = TpVar y
      utp = TpVar (unfoldTypeName y)
      dat = makeUnfoldDatatype y us
      x = "%abc" -- targetName -- TODO
      sub_ps = map (\ (x, tp) -> (x, derefunSubst Refun y tp))
      alls = zipWith3 (\ (fvs, tp) cs i -> (fvs, tp, cs, i)) us css [0..]
      cscs = map (\ (fvs, tp, cs, i) ->
                    let ps = sub_ps (Map.toList fvs)
                        g' = \ xps -> ctxtDeclArgs g (xps ++ ps)
                        cs' = map (\ (Case cx cps ctm) -> Case cx (sub_ps cps)
                                    (derefunTerm Refun (g' cps) y ctm)) cs in
                      TmVarG CtorVar (unfoldCtorName y i)
                        [(joinLams ps
                           (TmCase (TmVarL x ytp) ytp cs' tp),
                          joinArrows (map snd ps) tp)] utp) alls
      fun = ProgFun (unfoldName y) [] (TmLam x ytp (ambAll cscs utp) utp) (TpArr ytp utp)
  in
    (dat, fun)

-- See `disentangleFile`
disentangleTerm :: Var -> [(FreeVars, Type)] -> Term -> DisentangleM Term
disentangleTerm rtp cases = h where
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
    | tp1 == TpVar rtp =
      h tm >>= \ tm' ->
      mapCasesM (const h) cs >>= \ cs' ->
      State.get >>= \ unfolds ->
      let i = length unfolds
          x' = "%def" -- targetName -- TODO
          cs'' = map (\ (j, (cfvs, ctp2)) -> let ps = Map.toList cfvs; arrtp = joinArrows (map snd ps) ctp2 in Case (unfoldCtorName rtp j) [(x', arrtp)] (if i == j then (joinApps (TmVarL x' arrtp) (paramsToArgs ps)) else TmSamp DistFail tp2 {-TmApp (TmSamp DistFail (TpArr arrtp tp2)) (TmVarL x' arrtp) arrtp tp2-}))
                    (enumerate cases)
          rtm = TmCase tm (TpVar (unfoldTypeName rtp)) cs'' tp2
      in
        State.put (unfolds ++ [cs']) >>
        pure rtm
    | otherwise =
      pure TmCase <*> h tm <*> pure tp1 <*> mapCasesM (const h) cs <*> pure tp2
  h (TmSamp d tp) =
    pure (TmSamp d tp)
  h (TmAmb tms tp) = pure TmAmb <*> mapM h tms <*> pure tp

type DefoldM a = State.State [Term] a

defoldTerm :: Var -> Term -> DefoldM Term
defoldTerm rtp = h where
  h :: Term -> DefoldM Term
  h (TmVarL x tp) = pure (TmVarL x tp)
  h (TmVarG gv x as tp)
    | gv == CtorVar && tp == TpVar rtp =
        mapArgsM h as >>= \ as' ->
        State.get >>= \ fs ->
        let fvs = Map.toList (freeVarsArgs' as')
            cname = foldCtorName rtp (length fs)
            tname = foldTypeName rtp
            aname = applyName rtp
            fld = TmVarG CtorVar cname (paramsToArgs fvs) (TpVar tname)
        in
          State.put (fs ++ [TmVarG CtorVar x as' (TpVar rtp)]) >> -- TODO: maybe switch fs ++ [new] to [new] ++ fs
          return (TmVarG DefVar aname [(fld, TpVar tname)] (TpVar rtp))
    | otherwise = pure (TmVarG gv x) <*> mapArgsM h as <*> pure tp
  h (TmLam x tp tm tp') = pure (TmLam x tp) <*> h tm <*> pure tp'
  h (TmApp tm1 tm2 tp2 tp) = pure TmApp <*> h tm1 <*> h tm2 <*> pure tp2 <*> pure tp
  h (TmLet x xtm xtp tm tp) = pure (TmLet x) <*> h xtm <*> pure xtp <*> h tm <*> pure tp
  h (TmCase tm tp1 cs tp2) = pure TmCase <*> h tm <*> pure tp1 <*> mapCasesM (const h) cs <*> pure tp2
  h (TmSamp d tp) = pure (TmSamp d tp)
  h (TmAmb tms tp) = pure TmAmb <*> mapM h tms <*> pure tp


makeDefold :: Ctxt  -> Var -> [Term] -> (Prog, Prog)
makeDefold g y tms =
  let fname = applyName y
      tname = foldTypeName y
      x = "%ghi" -- targetName -- TODO
      ftp = TpVar tname
      ps = [(x, ftp)]
      casesf = \ (i, tm) -> let ps' = Map.toList (freeVars' tm) in Case (foldCtorName y i) ps' (derefunTerm Defun (ctxtDeclArgs g ps') y tm)
      cases = map casesf (enumerate tms)
      ctors = map (\ (Case x ps tm) -> Ctor x (map snd ps)) cases
      tm = TmCase (TmVarL x ftp) ftp cases (TpVar y)
  in
    (ProgData tname ctors,
     ProgFun fname [] (joinLams ps tm) (joinArrows (map snd ps) (TpVar y)))


derefoldThis :: DeRe -> Var -> Progs -> (Progs, Prog, Prog)
derefoldThis Defun rtp ps =
  let --fvs_xs = collectFoldsFile rtp ps
      (ps', fs) = State.runState (mapProgsM (defoldTerm rtp) ps) []
      ps'' = derefunProgsTypes Defun rtp ps'
      g = ctxtDefProgs ps''
      (dat, fun) = makeDefold g rtp fs
  in
    (ps'', dat, fun)
derefoldThis Refun rtp ps =
  let fvs_tps = collectUnfoldsFile rtp ps
      (ps', cs) = State.runState (mapProgsM (disentangleTerm rtp fvs_tps) ps) []
      ps'' = derefunProgsTypes Refun rtp ps'
      g = ctxtDefProgs ps''
      (dat, fun) = makeDisentangle g rtp fvs_tps cs
  in
    (ps'', dat, fun)

derefoldThis' :: DeRe -> Var -> Progs -> Progs
derefoldThis' dr rtp ps =
  let (ps', dat, fun) = derefoldThis dr rtp ps in
    insertProgs rtp dat fun (derefun dr rtp [dat, fun] ps')

derefoldThese :: [(Var, DeRe)] -> Progs -> Progs
derefoldThese = flip $ foldl $ \ ps (rtp, dr) -> derefoldThis' dr rtp ps

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
    | dr == Refun && gv == CtorVar && tp == TpVar rtp =
      (TmVarG DefVar unfoldN [(TmVarG gv x (h_as as) tp, tp)] (TpVar unfoldTypeN), TpVar unfoldTypeN)
    | dr == Defun && gv == DefVar && x == applyN =
      let [(etm, etp)] = as in h etm
    | otherwise =
      maybe2 (ctxtLookupTerm g x) (TmVarG gv x (h_as as) tp, tp) $ \ (_, tp') ->
      let (tps, end) = splitArrows tp'
          tp'' = joinArrows (drop (length as) tps) end in
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
    | otherwise =
        let (tm1', tp1') = h tm1
            cs' = map (\ (Case x ps xtm) -> Case x (h_ps ps) (fst (h xtm))) cs
            tp2' = case cs' of [] -> sub tp2; (Case x ps xtm : _) -> getType xtm in
          (TmCase tm1' tp1' cs' tp2', tp2')
  h (TmSamp d tp) = (TmSamp d tp, tp)
  h (TmAmb tms tp) =
    let tms' = map h tms
        tp' = if null tms' then sub tp else snd (head tms') in
      (TmAmb (map fst tms') tp', tp')



derefunProgTypes :: DeRe -> Var -> Prog -> Prog
derefunProgTypes dr rtp (ProgFun x ps tm tp) = ProgFun x (map (fmap (derefunSubst dr rtp)) ps) tm (derefunSubst dr rtp tp)
derefunProgTypes dr rtp (ProgExtern x xp ps tp) = ProgExtern x xp ps tp
derefunProgTypes dr rtp (ProgData y cs) = ProgData y (map (\ (Ctor x tps) -> Ctor x (map (derefunSubst dr rtp) tps)) cs)

derefunProgsTypes :: DeRe -> Var -> Progs -> Progs
derefunProgsTypes dr rtp (Progs ps end) =
  Progs (map (derefunProgTypes dr rtp) ps) end

derefunProg' :: DeRe -> Ctxt -> Var -> Prog -> Prog
derefunProg' dr g rtp (ProgFun x ps tm tp) = ProgFun x ps (derefunTerm dr g rtp tm) tp
derefunProg' dr g rtp (ProgExtern x xp ps tp) = ProgExtern x xp ps tp
derefunProg' dr g rtp (ProgData y cs) = ProgData y cs

derefun :: DeRe -> Var -> [Prog] -> Progs -> Progs
derefun dr rtp new_ps (Progs ps end) =
  let g = ctxtDefProgs (Progs (ps ++ new_ps) end) in
    Progs (map (derefunProg' dr g rtp) ps) (derefunTerm dr g rtp end)

defun :: Var -> [Prog] -> Progs -> Progs
defun = derefun Defun

refun :: Var -> [Prog] -> Progs -> Progs
refun = derefun Refun

insertProgs' :: Var -> Prog -> Prog -> [Prog] -> [Prog]
insertProgs' rtp dat fun [] = []
insertProgs' rtp dat fun (ProgData y cs : ds) = if y == rtp then ProgData y cs : dat : fun : ds else ProgData y cs : insertProgs' rtp dat fun ds
insertProgs' rtp dat fun (d : ds) = d : insertProgs' rtp dat fun ds

insertProgs :: Var -> Prog -> Prog -> Progs -> Progs
insertProgs rtp dat fun (Progs ds end) = Progs (insertProgs' rtp dat fun ds) end

whichDR :: Progs -> [(Var, DeRe)]
whichDR ps =
  let recs = getRecTypes ps in
--    map (\ rtp -> (rtp, Refun)) recs -- TODO
    zip recs [Defun, Refun]

-- TODO: figure out naming of fold/unfold functions (fold/apply or apply/unfold?)
elimRecTypes :: Progs -> Either String Progs
elimRecTypes ps = return (derefoldThese (whichDR ps) ps)
