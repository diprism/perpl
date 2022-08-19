module Transform.DR where
import qualified Data.Map as Map
import qualified Control.Monad.State.Lazy as State
import Data.List
import Struct.Lib
import Util.Helpers
import Scope.Free (getRecursiveTypeNames)
import Scope.Subst (Substitutable, SubT(SubVar), subst, FreeVars, freeVars)
import Scope.Ctxt (Ctxt, ctxtDefProgs, ctxtDeclArgs, ctxtLookupTerm, ctxtLookupType)
import Scope.Fresh (newVar)
import Scope.Name

-- Returns the free local variables of a Substitutable.

-- By the time defunctionalization/refunctionalization occurs, there
-- are no more type or tag variables, and TmVarGs are currently not
-- included in freeVars. So freeVarLs just calls freeVars.

freeVarLs :: Substitutable a => a -> FreeVars
freeVarLs = freeVars

-- Collects the free variables of all the cases in
-- a case-of over something with type rtp
collectUnfolds :: Var -> Term -> [(FreeVars, Type)]
collectUnfolds rtp (TmVarL x tp) = []
collectUnfolds rtp (TmVarG gv x _ _ as tp) = concatMap (\ (atm, atp) -> collectUnfolds rtp atm) as
collectUnfolds rtp (TmLam x tp tm tp') = collectUnfolds rtp tm
collectUnfolds rtp (TmApp tm1 tm2 tp2 tp) = collectUnfolds rtp tm1 ++ collectUnfolds rtp tm2
collectUnfolds rtp (TmLet x xtm xtp tm tp) = collectUnfolds rtp xtm ++ collectUnfolds rtp tm
collectUnfolds rtp (TmCase tm (y, _, _) cs tp) =
  let fvs = freeVarLs cs
      this = if y == rtp then [(fvs, tp)] else [] in
    collectUnfolds rtp tm
      ++ concatMap (\ (Case cx cps ctm) -> collectUnfolds rtp ctm) cs
      ++ this
collectUnfolds rtp (TmAmb tms tp) = concatMap (collectUnfolds rtp) tms
collectUnfolds rtp (TmFactor wt tm tp) = collectUnfolds rtp tm
collectUnfolds rtp (TmProd am as) = concatMap (\ (atm, atp) -> collectUnfolds rtp atm) as
collectUnfolds rtp (TmElimMultiplicative tm ps tm' tp) = collectUnfolds rtp tm ++ collectUnfolds rtp tm'
collectUnfolds rtp (TmElimAdditive tm n i p tm' tp) = collectUnfolds rtp tm ++ collectUnfolds rtp tm'
collectUnfolds rtp (TmEqs tms) = concatMap (collectUnfolds rtp) tms

-- Collects all the usages of constructors for type rtp,
-- returning the ctor name along with the free vars used
-- in its args
collectFolds :: Var -> Term -> [(Var, FreeVars)]
collectFolds rtp (TmVarL x tp) = []
collectFolds rtp (TmVarG gv x _ _ as tp) =
  let this = if TpData rtp [] [] == tp && gv == GlCtor then [(x, freeVarLs (fsts as))] else [] in
    concatMap (\ (atm, atp) -> collectFolds rtp atm) as ++ this
collectFolds rtp (TmLam x tp tm tp') = collectFolds rtp tm
collectFolds rtp (TmApp tm1 tm2 tp2 tp) = collectFolds rtp tm1 ++ collectFolds rtp tm2
collectFolds rtp (TmLet x xtm xtp tm tp) = collectFolds rtp xtm ++ collectFolds rtp tm
collectFolds rtp (TmCase tm y cs tp) = collectFolds rtp tm ++ concatMap (\ (Case cx cps ctm) -> collectFolds rtp ctm) cs
collectFolds rtp (TmAmb tms tp) = concatMap (collectFolds rtp) tms
collectFolds rtp (TmFactor wt tm tp) = collectFolds rtp tm
collectFolds rtp (TmProd am as) = concatMap (\ (atm, atp) -> collectFolds rtp atm) as
collectFolds rtp (TmElimMultiplicative tm ps tm' tp) = collectFolds rtp tm ++ collectFolds rtp tm'
collectFolds rtp (TmElimAdditive tm n i p tm' tp) = collectFolds rtp tm ++ collectFolds rtp tm'
collectFolds rtp (TmEqs tms) = concatMap (collectFolds rtp) tms

-- Runs collect[Un]folds on a Prog
collectProg :: (Term -> [a]) -> Prog -> [a]
collectProg f (ProgFun _ _ tm _) = f tm
collectProg f _ = []

-- Runs collect[Un]folds on a file
collectFile :: (Term -> [a]) -> Progs -> [a]
collectFile f (Progs ps end) = concatMap (collectProg f) ps ++ f end

-- See collectUnfolds
collectUnfoldsFile = collectFile . collectUnfolds

-- See collectFolds
collectFoldsFile = collectFile . collectFolds

-- Makes the _UnfoldY_ datatype, given results from collectUnfolds
makeUnfoldDatatype :: Var -> [(FreeVars, Type)] -> Prog
makeUnfoldDatatype y us = ProgData (refunTypeName y) [Ctor (refunCtorName y) [TpProd Additive [joinArrows (Map.elems fvs) tp | (fvs, tp) <- us]]]

-- Makes the _FoldY_ datatype, given results from collectFolds
--makeFoldDatatype :: Var -> [(Var, FreeVars)] -> Prog
--makeFoldDatatype y fs = ProgData (defunTypeName y) [Ctor (defunCtorName y i) (snds (Map.toList fvs)) | (i, (x, fvs)) <- enumerate fs]

-- Makes the "unapply" function and Unfold datatype
makeDisentangle :: Ctxt -> Var -> [(FreeVars, Type)] -> [[Case]] -> (Prog, Prog)
makeDisentangle g y us css =
  let ytp = TpData y [] []
      utp = TpData (refunTypeName y) [] []
      dat = makeUnfoldDatatype y us
      x = newVar localName g
      sub_ps ps = [(x, derefunSubst Refun y tp) | (x, tp) <- ps]
      alls = zipWith3 (\ (fvs, tp) cs i -> (fvs, tp, cs, i)) us css [0..]
      cscs = [let ps = sub_ps (Map.toList fvs)
                  g' = \ xps -> ctxtDeclArgs g (xps ++ ps)
                  cs' = [Case cx (sub_ps cps) (derefunTerm Refun (g' cps) y ctm)
                        | Case cx cps ctm <- cs] in
                 (joinLams ps (TmCase (TmVarL x ytp) (y, [], []) cs' tp),
                   joinArrows (tpUnit : snds ps) tp)
             | (fvs, tp, cs, i) <- alls]
      fun = ProgFun (unapplyName y) [(x, ytp)] (TmVarG GlCtor (refunCtorName y) [] [] [(TmProd Additive cscs, TpProd Additive (snds cscs))] utp) utp -- (TpArr ytp utp)
  in
    (dat, fun)

-- Makes the "apply" function and Fold datatype
makeDefold :: Ctxt  -> Var -> [Term] -> (Prog, Prog)
makeDefold g y tms =
  let fname = applyName y
      tname = defunTypeName y
      x = newVar localName g
      ftp = TpData tname [] []
      ps = [(x, ftp)]
      casesf = \ (i, tm) -> let ps' = Map.toList (freeVarLs tm) in Case (defunCtorName y i) ps' (derefunTerm Defun (ctxtDeclArgs g ps') y tm)
      cases = map casesf (enumerate tms)
      ctors = [Ctor x (snds ps) | Case x ps tm <- cases]
      tm = TmCase (TmVarL x ftp) (tname, [], []) cases (TpData y [] [])
  in
--    error (tname ++ " | " ++ show ctors ++ " | " ++ show cases)
    (ProgData tname ctors,
     ProgFun fname ps tm (TpData y [] []))

--------------------------------------------------

-- Replaces all case-ofs on a certain datatype with calls to
-- its "unapply" function
type DisentangleM a = State.State [[Case]] a

-- See `disentangleFile`
disentangleTerm :: Var -> [(FreeVars, Type)] -> Term -> DisentangleM Term
disentangleTerm rtp cases = h where
  h :: Term -> DisentangleM Term
  h (TmVarL x tp) = pure (TmVarL x tp)
  h (TmVarG gv x _ _ as tp) =
    pure (TmVarG gv x [] []) <*> mapArgsM h as <*> pure tp
  h (TmLam x tp tm tp') =
    pure (TmLam x tp) <*> h tm <*> pure tp'
  h (TmApp tm1 tm2 tp2 tp) =
    pure TmApp <*> h tm1 <*> h tm2 <*> pure tp2 <*> pure tp
  h (TmLet x xtm xtp tm tp) =
    pure (TmLet x) <*> h xtm <*> pure xtp <*> h tm <*> pure tp
  h (TmCase tm (y, _, _) cs tp)
    -- case tm of ...
    --   becomes
    -- case tm of _unfoldY_ x' -> let <_, ..., x'', ..., _> = x' in x''
    | y == rtp =
      h tm >>= \ tm' ->
      mapCasesM (\ _ _ -> h) cs >>= \ cs' ->
      State.get >>= \ unfolds ->
      let i = length unfolds
          -- Because there are no other free variables, this is safe
          x' = localName
          x'' = localName
          get_ps = \ (cfvs, ctp2) -> Map.toList cfvs
          get_as = \ (cfvs, ctp2) -> paramsToArgs (Map.toList cfvs)
          get_arr = \ (cfvs, ctp2) -> joinArrows (snds (get_ps (cfvs, ctp2))) ctp2
          xtps = map get_arr cases
          xtp = TpProd Additive xtps
          cs'' = [Case (refunCtorName rtp) [(x', xtp)] (let cfvstp2 = cases !! i in joinApps (TmElimAdditive (TmVarL x' xtp) (length xtps) i (x'', xtps !! i) (TmVarL x'' (xtps !! i)) (xtps !! i)) (get_as cfvstp2))]
          rtm = TmCase tm (refunTypeName rtp, [], []) cs'' tp
      in
        State.put (unfolds ++ [cs']) >>
        pure rtm
    | otherwise =
      pure TmCase <*> h tm <*> pure (y, [], []) <*> mapCasesM (\ _ _ -> h) cs <*> pure tp
  h (TmAmb tms tp) =
    pure TmAmb <*> mapM h tms <*> pure tp
  h (TmFactor wt tm tp) =
    pure (TmFactor wt) <*> h tm <*> pure tp
  h (TmProd am as) =
    pure (TmProd am) <*> mapArgsM h as
  h (TmElimAdditive tm n i p tm' tp) =
    pure TmElimAdditive <*> h tm <*> pure n <*> pure i <*> pure p <*> h tm' <*> pure tp
  h (TmElimMultiplicative tm ps tm' tp) =
    pure TmElimMultiplicative <*> h tm <*> pure ps <*> h tm' <*> pure tp
  h (TmEqs tms) =
    pure TmEqs <*> mapM h tms

--------------------------------------------------

-- Replaces all constructor calls for a certain datatype with calls
-- to its "apply" function
type DefoldM a = State.State [Term] a

defoldTerm :: Var -> Term -> DefoldM Term
defoldTerm rtp = h where
  h :: Term -> DefoldM Term
  h (TmVarL x tp) = pure (TmVarL x tp)
  h (TmVarG gv x _ _ as tp)
    | gv == GlCtor && tp == TpData rtp [] [] =
        mapArgsM h as >>= \ as' ->
        State.get >>= \ fs ->
        let fvs = Map.toList (freeVarLs (fsts as'))
            cname = defunCtorName rtp (length fs)
            tname = defunTypeName rtp
            aname = applyName rtp
            fld = TmVarG GlCtor cname [] [] (paramsToArgs fvs) (TpData tname [] [])
        in
          State.put (fs ++ [TmVarG GlCtor x [] [] as' (TpData rtp [] [])]) >>
          return (TmVarG GlFun aname [] [] [(fld, TpData tname [] [])] (TpData rtp [] []))
    | otherwise = pure (TmVarG gv x [] []) <*> mapArgsM h as <*> pure tp
  h (TmLam x tp tm tp') = pure (TmLam x tp) <*> h tm <*> pure tp'
  h (TmApp tm1 tm2 tp2 tp) = pure TmApp <*> h tm1 <*> h tm2 <*> pure tp2 <*> pure tp
  h (TmLet x xtm xtp tm tp) = pure (TmLet x) <*> h xtm <*> pure xtp <*> h tm <*> pure tp
  h (TmCase tm y cs tp) = pure TmCase <*> h tm <*> pure y <*> mapCasesM (\ _ _ -> h) cs <*> pure tp
  h (TmAmb tms tp) = pure TmAmb <*> mapM h tms <*> pure tp
  h (TmFactor wt tm tp) = pure (TmFactor wt) <*> h tm <*> pure tp
  h (TmProd am as) =
    pure (TmProd am) <*> mapArgsM h as
  h (TmElimAdditive tm n i p tm' tp) =
    pure TmElimAdditive <*> h tm <*> pure n <*> pure i <*> pure p <*> h tm' <*> pure tp
  h (TmElimMultiplicative tm ps tm' tp) =
    pure TmElimMultiplicative <*> h tm <*> pure ps <*> h tm' <*> pure tp
  h (TmEqs tms) =
    pure TmEqs <*> mapM h tms

--------------------------------------------------

data DeRe = Defun | Refun
  deriving (Eq, Show)

-- Substitute from a datatype name to its Unfold/Fold datatype's name
derefunSubst :: DeRe -> Var -> Type -> Type
derefunSubst dr rtp = subst (Map.fromList [(rtp, SubVar (if dr == Defun then defunTypeName rtp else refunTypeName rtp))])

defunTerm = derefunTerm Defun
refunTerm = derefunTerm Refun

-- De- or refunctionalizes a term (see examples at EOF for more info)
derefunTerm :: DeRe -> Ctxt -> Var -> Term -> Term
derefunTerm dr g rtp = fst . h where

  foldTypeN = defunTypeName rtp
  applyN = applyName rtp
  unfoldN = unapplyName rtp
  unfoldTypeN = refunTypeName rtp
  
  sub = derefunSubst dr rtp

  h_ps :: [Param] -> [Param]
  h_ps = map (fmap sub)
  h_as :: [Arg] -> [Arg]
  h_as = map (h . fst)

  h :: Term -> (Term, Type)
  h = toArg . h'
  
  h' :: Term -> Term
  h' (TmVarL x tp) = let tp' = sub tp in TmVarL x tp'
  h' (TmVarG gv x _ _ as tp)
    | dr == Refun && gv == GlCtor && tp == TpData rtp [] [] =
      TmVarG GlFun unfoldN [] [] [(TmVarG gv x [] [] (h_as as) tp, tp)] (TpData unfoldTypeN [] [])
    | dr == Defun && gv == GlFun && x == applyN =
      let [(etm, etp)] = as in h' etm
    | otherwise =
      maybe2 (ctxtLookupTerm g x) (TmVarG gv x [] [] (h_as as) tp) $ \ tp' ->
      let (tps, end) = splitArrows tp'
          tp'' = joinArrows (drop (length as) tps) end in
        TmVarG gv x [] [] (h_as as) tp''
  h' (TmLam x tp1 tm tp2) =
    let tp1' = sub tp1
        (tm', tp2') = h tm in
      TmLam x tp1' tm' tp2'
  h' (TmApp tm1 tm2 tp2 tp) =
    let (tm1', TpArr _ tp') = h tm1
        (tm2', tp2') = h tm2 in
      TmApp tm1' tm2' tp2' tp'
  h' (TmLet x xtm xtp tm tp) =
    let (xtm', xtp') = h xtm
        (tm', tp') = h tm in
    TmLet x xtm' xtp' tm' tp'
  h' (TmCase tm1 (tp1, _, _) cs tp2)
    | dr == Defun && tp1 == rtp =
        let (tm1', tp1') = h tm1
            cs' = [Case x (h_ps ps) (fst (h xtm)) | Case x ps xtm <- cs]
            tp2' = case cs' of [] -> sub tp2; (Case x ps xtm : _) -> typeof xtm in
          TmCase (TmVarG GlFun applyN [] [] [(tm1', tp1')] (TpData rtp [] [])) (rtp, [], []) cs' tp2'
    | otherwise =
        let (tm1', TpData tp1' [] []) = h tm1
            cs' = [Case x (h_ps ps) (fst (h xtm)) | Case x ps xtm <- cs]
            tp2' = case cs' of [] -> sub tp2; (Case x ps xtm : _) -> typeof xtm in
          TmCase tm1' (tp1', [], []) cs' tp2'
  h' (TmAmb tms tp) =
    let tms' = map h tms
        tp' = if null tms' then sub tp else snd (head tms') in
      TmAmb (fsts tms') tp'
  h' (TmFactor wt tm tp) = let (tm', tp') = h tm in TmFactor wt tm' tp'
  h' (TmProd am as) =
    TmProd am [h tm | (tm, _) <- as]
  h' (TmElimMultiplicative tm ps tm' tp) =
    let (tm2, TpProd Multiplicative tps) = h tm
        (tm2', tp) = h tm'
        xs = [x | (x, _) <- ps]
        ps' = zip xs tps
    in
      TmElimMultiplicative tm2 ps' tm2' tp
  h' (TmElimAdditive tm n i (x,_) tm' tp) =
    let (tm2, TpProd Additive tps) = h tm
        (tm2', tp) = h tm'
    in
      TmElimAdditive tm2 n i (x, tps!!i) tm2' tp
  h' (TmEqs tms) =
    TmEqs [h' tm | tm <- tms]

derefunProgTypes :: DeRe -> Var -> Prog -> Prog
derefunProgTypes dr rtp (ProgFun x ps tm tp) = ProgFun x (map (fmap (derefunSubst dr rtp)) ps) tm (derefunSubst dr rtp tp)
derefunProgTypes dr rtp (ProgExtern x ps tp) = ProgExtern x ps tp
derefunProgTypes dr rtp (ProgData y cs) = ProgData y [Ctor x [derefunSubst dr rtp tp | tp <- tps] | Ctor x tps <- cs]

derefunProgsTypes :: DeRe -> Var -> Progs -> Progs
derefunProgsTypes dr rtp (Progs ps end) =
  Progs (map (derefunProgTypes dr rtp) ps) end

derefunProg' :: DeRe -> Ctxt -> Var -> Prog -> Prog
derefunProg' dr g rtp (ProgFun x ps tm tp) = ProgFun x ps (derefunTerm dr g rtp tm) tp
derefunProg' dr g rtp (ProgExtern x ps tp) = ProgExtern x ps tp
derefunProg' dr g rtp (ProgData y cs) = ProgData y cs

derefun :: DeRe -> Var -> [Prog] -> Progs -> Either String Progs
derefun dr rtp new_ps (Progs ps end) =
  let g = ctxtDefProgs (Progs (ps ++ new_ps) end)
      rps = (map (derefunProg' dr g rtp) ps)
      rtm = (derefunTerm dr g rtp end)
      --dr' = if dr == Defun then "defunctionalize" else "refunctionalize"
      --emsg = "Failed to " ++ dr' ++ " " ++ rtp
  in
    return (Progs rps rtm)

derefunThis :: DeRe -> Var -> Progs -> (Progs, Prog, Prog)
derefunThis Defun rtp ps =
  let (ps', fs) = State.runState (mapProgsM (defoldTerm rtp) ps) []
      ps'' = derefunProgsTypes Defun rtp ps'
      g = ctxtDefProgs ps''
      (dat, fun) = makeDefold g rtp fs
  in
    (ps'', dat, fun)
derefunThis Refun rtp ps =
  let fvs_tps = collectUnfoldsFile rtp ps
      (ps', cs) = State.runState (mapProgsM (disentangleTerm rtp fvs_tps) ps) []
      ps'' = derefunProgsTypes Refun rtp ps'
      g = ctxtDefProgs ps''
      (dat, fun) = makeDisentangle g rtp fvs_tps cs
  in
    (ps'', dat, fun)

derefunThis' :: DeRe -> Var -> Progs -> Either String Progs
derefunThis' dr rtp ps =
  let (ps', dat, fun) = derefunThis dr rtp ps in
    derefun dr rtp [dat, fun] ps' >>=
    return . insertProgs rtp dat fun 

derefunThese :: Progs -> [(Var, DeRe)] -> Either String Progs
derefunThese ps recs = foldl (\ ps (rtp, dr) -> ps >>= derefunThis' dr rtp) (return ps) recs

insertProgs' :: Var -> Prog -> Prog -> [Prog] -> [Prog]
insertProgs' rtp dat fun [] = []
insertProgs' rtp dat fun (ProgData y cs : ds) | y == rtp = ProgData y cs : dat : fun : ds
insertProgs' rtp dat fun (d : ds) = d : insertProgs' rtp dat fun ds

-- Inserts new Fold/Unfold progs right after the datatype they correspond to
insertProgs :: Var -> Prog -> Prog -> Progs -> Progs
insertProgs rtp dat fun (Progs ds end) = Progs (insertProgs' rtp dat fun ds) end

--------------------------------------------------

-- Computes whether to de- or refunctionalize each recursive datatype

data RecDeps = RecDeps { defunDeps :: [Var], refunDeps :: [Var] }
  deriving Show
type RecEdges = Map Var RecDeps

recDeps :: Ctxt -> [Var] -> Type -> [Var]
recDeps g recs (TpData y _ _)
  | y `elem` recs = [y]
  | otherwise = maybe []
      (nub . concatMap (\ (Ctor _ tps) -> concatMap (recDeps g recs) tps))
      (ctxtLookupType g y)
recDeps g recs (TpArr tp1 tp2) = nub (recDeps g recs tp1 ++ recDeps g recs tp2)
recDeps g recs (TpProd am tps) = nub (concatMap (recDeps g recs) tps)
recDeps g recs  _ = []

getRefunDeps :: Ctxt -> [Var] -> [(FreeVars, Type)] -> [Var]
getRefunDeps g recs =
  nub . foldr (\ (fvs, tp) rs -> foldr (\ tp rs -> recDeps g recs tp ++ rs) rs (tp : Map.elems fvs)) []

getDefunDeps :: Ctxt -> [Var] -> [(Var, FreeVars)] -> [Var]
getDefunDeps g recs =
  nub . foldr (\ (_, fvs) rs -> foldr (\ tp rs -> recDeps g recs tp ++ rs) rs (Map.elems fvs)) []

getDeps :: Ctxt -> [Var] -> Progs -> Var -> RecDeps
getDeps g recs ps y = RecDeps {
  defunDeps = (getDefunDeps g recs (collectFoldsFile y ps)),
  refunDeps = (getRefunDeps g recs (collectUnfoldsFile y ps))
}

initGraph :: Ctxt -> Progs -> [Var] -> RecEdges
initGraph g ps recs = Map.fromList (zip recs (map (getDeps g recs ps) recs))

-- Tests if all this node's deps are already in the set of chosen nodes
tryPickDR :: [(Var, DeRe)] -> Var -> RecDeps -> [(Var, DeRe)] -> Maybe (Var, DeRe)
tryPickDR explicit_drs rtp (RecDeps ds rs) chosen =
  maybe
    (h (rtp, Defun) ds chosen |?| h (rtp, Refun) rs chosen)
    (\ dr -> h (rtp, dr) (if dr == Defun then ds else rs) chosen)
    (lookup rtp explicit_drs)
  where
    h :: (Var, DeRe) -> [Var] -> [(Var, DeRe)] -> Maybe (Var, DeRe)
    h xdr ys chosen = mapM (\ y -> lookup y chosen) ys >> Just xdr

-- Picks a node that has all its dependencies already in the set of chosen nodes
pickNextDR :: [(Var, DeRe)] -> RecEdges -> [(Var, DeRe)] -> Maybe (Var, DeRe)
pickNextDR explicit_drs res drs = Map.foldrWithKey (\ rtp rds dr_else -> tryPickDR explicit_drs rtp rds drs |?| dr_else) Nothing res

-- Error message for when no DR sequence can be found
spanGraphError :: RecEdges -> [(Var, DeRe)] -> Either String a
spanGraphError res chosen =
  Left $ "Failed to resolve the following dependencies:\n" ++
    (intercalate "\n" $ uncurry depmsg <$> Map.toList res)
    where
      depmsg :: Var -> RecDeps -> String
      depmsg rtp (RecDeps defs refs) = depstr 'D' rtp defs ++ "\n" ++ depstr 'R' rtp refs
      
      relevantDeps :: [Var] -> [Var]
      relevantDeps = filter $ flip Map.member res
      
      depstr :: Char -> Var -> [Var] -> String
      depstr dr (Var name) deps = dr : "[" ++ name ++ "] <- " ++ intercalate ", " (show <$> relevantDeps deps)

-- Greedily pops nodes from the graph that satisfy tryPickDR until none remain,
-- returning the recursive datatype names and whether to de- or refunctionalize them
spanGraph :: [(Var, DeRe)] -> RecEdges -> Either String [(Var, DeRe)]
spanGraph explicit_drs res =
  case [ rtp | (rtp,_) <- explicit_drs, Map.notMember rtp res ] of
    [] -> h [] res
    extras -> Left $ "No recursive datatype named " ++ intercalate " or " (show <$> extras) ++
                     case [ rtp | rtp <- Map.keys res, any (`isPrefixOf` (show rtp)) (show <$> extras) ] of
                       [] -> ""
                       actuals -> " (did you mean " ++ intercalate " or " (show <$> actuals) ++ "?)"
 where
  h :: [(Var, DeRe)] -> RecEdges -> Either String [(Var, DeRe)]
  h chosen res
    | null res = return (reverse chosen)
    | otherwise =
        maybe (spanGraphError res chosen)
          return (pickNextDR explicit_drs res chosen) >>= \ (rtp, dr) ->
        h ((rtp, dr) : chosen) (Map.delete rtp res)

-- Given some explicit datatypes to de- or refun, compute which to do on the rest
whichDR :: [(Var, DeRe)] -> Progs -> Either String [(Var, DeRe)]
whichDR explicit_drs ps =
  let g = ctxtDefProgs ps in
    spanGraph explicit_drs (initGraph g ps (getRecursiveTypeNames g))


--------------------------------------------------

-- TODO: figure out naming of fold/unfold functions (fold/apply or apply/unfold?)
-- Eliminates the recursive datatypes in a file, by de- or refunctionalizing them
elimRecTypes :: [(Var, DeRe)] -> Progs -> Either String Progs
elimRecTypes explicit_drs ps =
  whichDR explicit_drs ps >>=
  derefunThese ps



{- ======== Example ========
======== Original File ========

data Nat = zero | succ Nat;
data Bool = false | true;

define even : Nat -> Bool = \ n : Nat. case n of
  | zero -> true
  | succ n' -> (case n' of
    | zero -> false
    | succ n'' -> even n''
  );

even (succ (succ (succ zero)));

======== Defunctionalized File ========

data Nat = zero | succ FoldNat;

data FoldNat = foldNat_0 | foldNat_1 | foldNat_2 | foldNat_3;

define applyNat : FoldNat -> Nat = \ n : FoldNat. case n of
  | foldNat_0 -> zero
  | foldNat_1 -> succ foldNat_0
  | foldNat_2 -> succ foldNat_1
  | foldNat_3 -> succ foldNat_2;

data Bool = false | true;

define even : FoldNat -> Bool = \ n : FoldNat. case applyNat n of
  | zero -> true
  | succ n' -> (case applyNat n' of
    | zero -> false
    | succ n'' -> even n''
  );

even foldNat_3

======== Refunctionalized File ========

data Nat = zero | succ UnfoldNat;

data UnfoldNat = unfoldNat_0 Bool | unfoldNat_1 Bool;

define unapplyNat : Nat -> UnfoldNat =
  \ n : Nat. case sample amb : Bool of
    | false -> unfoldNat_0 (case n of
      | zero -> false
      | succ n'' -> even n''
    )
    | true  -> unfoldNat_1 (case n of
      | zero -> true
      | succ n' -> (case n' of
        | unfoldNat_0 b -> b
        | unfoldNat_1 b -> sample fail : Bool
      )
    );

data Bool = false | true;

define even : UnfoldNat -> Bool = \ n : UnfoldNat. case n of
  | unfoldNat_0 b -> sample fail : Bool
  | unfoldNat_1 b -> b;

even (unapplyNat (succ (unapplyNat (succ (unapplyNat (succ (unapplyNat zero)))))))

-}
