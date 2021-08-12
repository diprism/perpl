module RecType where
import qualified Data.Map as Map
import qualified Control.Monad.State.Lazy as State
import Data.List
import Exprs
import Util
import Free
import Ctxt
import Name
import Rename
import Show

--------------------------------------------------

-- Returns if any of a list of types end up referencing a var
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

-- Returns if y is a recursive datatype
isRecDatatype :: Ctxt -> Var -> Bool
isRecDatatype g y =
  maybe False (isRecType' g y . concatMap (\ (Ctor _ tps) -> tps)) (ctxtLookupType g y)

-- Returns if a type is a recursive datatype var
isRecType :: Ctxt -> Type -> Bool
isRecType g (TpVar y) = isRecDatatype g y
isRecType g _ = False

-- Returns the recursive datatypes in a file
getRecTypes' :: Ctxt -> [Prog] -> [Var]
getRecTypes' g (ProgData y cs : ds) =
  if isRecDatatype g y then y : getRecTypes' g ds else getRecTypes' g ds
getRecTypes' g (ProgFun x ps tm tp : ds) = getRecTypes' g ds
getRecTypes' g (ProgExtern x xp ps tp : ds) = getRecTypes' g ds
getRecTypes' g [] = []

-- Returns the recursive datatypes in a file
getRecTypes :: Progs -> [Var]
getRecTypes (Progs ds end) =
  getRecTypes' (ctxtDefProgs (Progs ds end)) ds

--------------------------------------------------

-- Collects the free variables of all the cases in
-- a case-of over something with type rtp
collectUnfolds :: Var -> Term -> [(FreeVars, Type)]
collectUnfolds rtp (TmVarL x tp) = []
collectUnfolds rtp (TmVarG gv x as tp) = concatMap (\ (atm, atp) -> collectUnfolds rtp atm) as
collectUnfolds rtp (TmLam x tp tm tp') = collectUnfolds rtp tm
collectUnfolds rtp (TmApp tm1 tm2 tp2 tp) = collectUnfolds rtp tm1 ++ collectUnfolds rtp tm2
collectUnfolds rtp (TmLet x xtm xtp tm tp) = collectUnfolds rtp xtm ++ collectUnfolds rtp tm
collectUnfolds rtp (TmCase tm y cs tp) =
  let fvs = freeVarsCases' cs
      this = if y == rtp then [(fvs, tp)] else [] in
    collectUnfolds rtp tm
      ++ concatMap (\ (Case cx cps ctm) -> collectUnfolds rtp ctm) cs
      ++ this
collectUnfolds rtp (TmSamp d tp) = []
collectUnfolds rtp (TmAmb tms tp) = concatMap (collectUnfolds rtp) tms

-- Collects all the usages of constructors for type rtp,
-- returning the ctor name along with the free vars used
-- in its args
collectFolds :: Var -> Term -> [(Var, FreeVars)]
collectFolds rtp (TmVarL x tp) = []
collectFolds rtp (TmVarG gv x as tp) =
  let this = if TpVar rtp == tp then [(x, freeVarsArgs' as)] else [] in
    concatMap (\ (atm, atp) -> collectFolds rtp atm) as ++ this
collectFolds rtp (TmLam x tp tm tp') = collectFolds rtp tm
collectFolds rtp (TmApp tm1 tm2 tp2 tp) = collectFolds rtp tm1 ++ collectFolds rtp tm2
collectFolds rtp (TmLet x xtm xtp tm tp) = collectFolds rtp xtm ++ collectFolds rtp tm
collectFolds rtp (TmCase tm y cs tp) = collectFolds rtp tm ++ concatMap (\ (Case cx cps ctm) -> collectFolds rtp ctm) cs
collectFolds rtp (TmSamp d tp) = []
collectFolds rtp (TmAmb tms tp) = concatMap (collectFolds rtp) tms

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

-- Makes the %UnfoldY% datatype, given results from collectUnfolds
makeUnfoldDatatype :: Var -> [(FreeVars, Type)] -> Prog
makeUnfoldDatatype y = ProgData (unfoldTypeName y) . map (\ (i, (fvs, tp)) -> Ctor (unfoldCtorName y i) [joinArrows (Map.elems fvs) tp]) . enumerate

-- Makes the %FoldY% datatype, given results from collectFolds
makeFoldDatatype :: Var -> [(Var, FreeVars)] -> Prog
makeFoldDatatype y = ProgData (foldTypeName y) . map (\ (i, (x, fvs)) -> Ctor (foldCtorName y i) (map snd (Map.toList fvs))) . enumerate

-- Makes the "unapply" function and Unfold datatype
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
                           (TmCase (TmVarL x ytp) y cs' tp),
                          joinArrows (map snd ps) tp)] utp) alls
      fun = ProgFun (unfoldName y) [] (TmLam x ytp (joinAmbs cscs utp) utp) (TpArr ytp utp)
  in
    (dat, fun)

-- Makes the "apply" function and Fold datatype
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
      tm = TmCase (TmVarL x ftp) tname cases (TpVar y)
  in
    (ProgData tname ctors,
     ProgFun fname [] (joinLams ps tm) (joinArrows (map snd ps) (TpVar y)))

--------------------------------------------------

-- Replaces all case-ofs on a certain datatype with calls to
-- its "unapply" function
type DisentangleM a = State.State [[Case]] a

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
  h (TmCase tm y cs tp)
    | y == rtp =
      h tm >>= \ tm' ->
      mapCasesM (const h) cs >>= \ cs' ->
      State.get >>= \ unfolds ->
      let i = length unfolds
          x' = "%def" -- targetName -- TODO
          cs'' = map (\ (j, (cfvs, ctp2)) -> let ps = Map.toList cfvs; arrtp = joinArrows (map snd ps) ctp2 in Case (unfoldCtorName rtp j) [(x', arrtp)] (if i == j then (joinApps (TmVarL x' arrtp) (paramsToArgs ps)) else TmSamp DistFail tp))
                    (enumerate cases)
          rtm = TmCase tm (unfoldTypeName rtp) cs'' tp
      in
        State.put (unfolds ++ [cs']) >>
        pure rtm
    | otherwise =
      pure TmCase <*> h tm <*> pure y <*> mapCasesM (const h) cs <*> pure tp
  h (TmSamp d tp) =
    pure (TmSamp d tp)
  h (TmAmb tms tp) = pure TmAmb <*> mapM h tms <*> pure tp

--------------------------------------------------

-- Replaces all constructor calls for a certain datatype with calls
-- to its "apply" function
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
          State.put (fs ++ [TmVarG CtorVar x as' (TpVar rtp)]) >>
          return (TmVarG DefVar aname [(fld, TpVar tname)] (TpVar rtp))
    | otherwise = pure (TmVarG gv x) <*> mapArgsM h as <*> pure tp
  h (TmLam x tp tm tp') = pure (TmLam x tp) <*> h tm <*> pure tp'
  h (TmApp tm1 tm2 tp2 tp) = pure TmApp <*> h tm1 <*> h tm2 <*> pure tp2 <*> pure tp
  h (TmLet x xtm xtp tm tp) = pure (TmLet x) <*> h xtm <*> pure xtp <*> h tm <*> pure tp
  h (TmCase tm y cs tp) = pure TmCase <*> h tm <*> pure y <*> mapCasesM (const h) cs <*> pure tp
  h (TmSamp d tp) = pure (TmSamp d tp)
  h (TmAmb tms tp) = pure TmAmb <*> mapM h tms <*> pure tp

--------------------------------------------------

data DeRe = Defun | Refun
  deriving (Eq, Show)

-- Substitute from a type var to its Unfold/Fold datatype
derefunSubst :: DeRe -> Var -> Type -> Type
derefunSubst dr rtp = substType rtp (if dr == Defun then foldTypeName rtp else unfoldTypeName rtp)

defunTerm = derefunTerm Defun
refunTerm = derefunTerm Refun

-- De- or refunctionalizes a term (see examples at EOF for more info)
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
    | dr == Defun && tp1 == rtp =
        let (tm1', tp1') = h tm1
            cs' = map (\ (Case x ps xtm) -> Case x (h_ps ps) (fst (h xtm))) cs
            tp2' = case cs' of [] -> sub tp2; (Case x ps xtm : _) -> getType xtm in
          (TmCase (TmVarG DefVar applyN [(tm1', tp1')] (TpVar rtp)) rtp cs' tp2', tp2')
    | otherwise =
        let (tm1', TpVar tp1') = h tm1
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

derefun :: DeRe -> Var -> [Prog] -> Progs -> Either String Progs
derefun dr rtp new_ps (Progs ps end) =
  let g = ctxtDefProgs (Progs (ps ++ new_ps) end)
      rps = (map (derefunProg' dr g rtp) ps)
      rtm = (derefunTerm dr g rtp end)
      dr' = if dr == Defun then "defunctionalize" else "refunctionalize"
      emsg = "Failed to " ++ dr' ++ " " ++ rtp
  in
    if typeIsRecursive (ctxtDefProgs (Progs (rps ++ new_ps) rtm)) (TpVar rtp) then Left emsg else return (Progs rps rtm)

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
insertProgs' rtp dat fun (ProgData y cs : ds) = if y == rtp then ProgData y cs : dat : fun : ds else ProgData y cs : insertProgs' rtp dat fun ds
insertProgs' rtp dat fun (d : ds) = d : insertProgs' rtp dat fun ds

-- Inserts new Fold/Unfold progs right after the datatype they correspond to
insertProgs :: Var -> Prog -> Prog -> Progs -> Progs
insertProgs rtp dat fun (Progs ds end) = Progs (insertProgs' rtp dat fun ds) end

--------------------------------------------------

-- Computes whether to de- or refunctionalize each recursive datatype

data RecDeps = RecDeps { defunDeps :: [Var], refunDeps :: [Var] }
  deriving Show
type RecEdges = Map.Map Var RecDeps

recDeps :: Ctxt -> [Var] -> Type -> [Var]
recDeps g recs (TpVar y)
  | y `elem` recs = [y]
  | otherwise = maybe []
      (nub . concatMap (\ (Ctor _ tps) -> concatMap (recDeps g recs) tps))
      (ctxtLookupType g y)
recDeps g recs (TpArr tp1 tp2) = nub (recDeps g recs tp1 ++ recDeps g recs tp2)

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

spanGraphError :: RecEdges -> [(Var, DeRe)] -> Either String a
spanGraphError res chosen =
  let ys = Map.keys res
      base_msg = "Failed to eliminate recursive datatype"
      plural_msg = if length ys > 1 then base_msg ++ "s" else base_msg
  in
    Left (foldl (\ s rtp -> s ++ " " ++ rtp) plural_msg ys)

-- Pops nodes from the graph that satisfy pickNextDR until none remain, returning
-- the recursive datatype names and whether to de- or refunctionalize them
spanGraph :: [(Var, DeRe)] -> RecEdges -> Either String [(Var, DeRe)]
spanGraph explicit_drs = h [] where
  h :: [(Var, DeRe)] -> RecEdges -> Either String [(Var, DeRe)]
  h chosen res
    | null res = return (reverse chosen)
    | otherwise =
        maybe (spanGraphError res chosen)
          return (pickNextDR explicit_drs res chosen) >>= \ (rtp, dr) ->
        h ((rtp, dr) : chosen) (Map.delete rtp res)

-- Given some explicit datatypes to de- or refun, compute which to
-- do on the rest
whichDR :: [(Var, DeRe)] -> Progs -> Either String [(Var, DeRe)]
whichDR explicit_drs ps =
  spanGraph explicit_drs (initGraph (ctxtDefProgs ps) ps (getRecTypes ps))


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
