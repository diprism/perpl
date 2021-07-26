module AffLin where
import Exprs
import Ctxt
import Util
import qualified Data.Map as Map
import Data.List


{- ====== Affine to Linear Functions ====== -}
-- These functions convert affine terms to
-- linear ones, where an affine term is one where
-- every bound var occurs at most once, and a
-- linear term is one where every bound var
-- occurs exactly once
type FreeVars = Map.Map Var Type

-- Uses x without changing the value or type of a term
-- For example, take x : Bool and some term tm that becomes
-- case x of false -> tm | true -> tm
discard :: Ctxt -> Var -> Type -> Term -> Term
discard g x (TpArr tp1 tp2) tm =
  error "This shouldn't happen" -- Should be TpMaybe if it is an arrow type
discard g x (TpVar y) tm = maybe2 (ctxtLookupType g y)
  (error ("In Free.hs/discard, unknown type var " ++ y))
  $ \ cs ->
      TmCase (TmVarL x (TpVar y)) (TpVar y)
        (map (\ (Ctor x' as) ->
                let as' = getArgs x' as in
                  Case x' as' (foldr (uncurry $ discard g) tm as'))
          cs) (getType tm)
discard g x (TpMaybe tp) tm =
  let x' = aff2linName x
      tp' = getType tm in
    tmElimMaybe (TmVarL x (TpMaybe tp)) tp tm
      (x', TmApp (TmApp (TmSamp DistFail (TpArr tp (TpArr tp' tp')))
                   (TmVarL x' tp) tp (TpArr tp' tp')) tm tp' tp') tp'
discard g x TpBool tm =
  tmIf (TmVarL x TpBool) tm tm (getType tm)

-- Discard a set of variables
discards :: Ctxt -> FreeVars -> Term -> Term
discards g fvs tm = Map.foldrWithKey (discard g) tm fvs

-- Convert the type of an affine term to what it will be when linear
-- That is, recursively change every T1 -> T2 to be Maybe (T1 -> T2)
aff2linTp :: Type -> Type
aff2linTp (TpVar y) = TpVar y
aff2linTp (TpArr tp1 tp2) = TpMaybe (TpArr (aff2linTp tp1) (aff2linTp tp2))
aff2linTp tp = error ("aff2linTp shouldn't see a " ++ show tp)

-- Make a case linear, returning the local vars that occur free in it
aff2linCase :: Ctxt -> Case -> (Case, FreeVars)
aff2linCase g (Case x as tm) =
  let (tm', fvs) = aff2linh (ctxtDeclArgs g as) tm
      -- Need to discard all "as" that do not occur free in "tm"
      tm'' = discards g (Map.difference (Map.fromList as) fvs) tm' in
    (Case x as tm'', foldr (Map.delete . fst) fvs as)

-- Make a term linear, returning the local vars that occur free in it
aff2linh :: Ctxt -> Term -> (Term, FreeVars)
aff2linh g (TmVarL x tp) =
  let ltp = aff2linTp tp in
    (TmVarL x ltp, Map.singleton x ltp)
aff2linh g (TmVarG gv x as y) =
  let (as', fvss) = unzip $ flip map as $
        \ (tm, tp) -> let (tm', xs) = aff2linh g tm in ((tm', aff2linTp tp), xs) in
  (TmVarG gv x as' y, Map.unions fvss)
  -- TODO: need to eta-expand global defs to have all arrows? And don't maybe-ify those lams? So that aff2lin on it doesn't convert those lams
aff2linh g (TmLam x tp tm tp') =
  let ltp = aff2linTp tp
      ltp' = aff2linTp tp'
      (tm', fvs) = aff2linh (ctxtDeclTerm g x ltp) tm
      fvs' = Map.delete x fvs
      tm'' = if Map.member x fvs then tm' else discard g x ltp tm'
      jtm = TmVarG CtorVar tmJustName
              [(TmLam x ltp tm'' ltp', TpArr ltp ltp')] (TpMaybe (TpArr ltp ltp'))
      ntm = discards g fvs'
              (TmVarG CtorVar tmNothingName [] (TpMaybe (TpArr ltp ltp'))) in
    (tmIf (TmSamp DistAmb TpBool) jtm ntm (TpMaybe (TpArr ltp ltp')), fvs')
aff2linh g (TmApp tm1 tm2 tp2 tp) =
  let (tm1', fvs1) = aff2linh g tm1
      (tm2', fvs2) = aff2linh g tm2
      ltp2 = aff2linTp tp2
      ltp = aff2linTp tp
      fvs = Map.union fvs1 fvs2
      ntm = TmApp (TmSamp DistFail (TpArr ltp2 ltp)) tm2' ltp2 ltp
      jx = etaName tmJustName 0
      jtm = TmApp (TmVarL jx (TpArr ltp2 ltp)) tm2' ltp2 ltp in
    (tmElimMaybe tm1' (TpArr ltp2 ltp) ntm (jx, jtm) ltp, fvs)
aff2linh g (TmLet x xtm xtp tm tp) =
  let xtp' = aff2linTp xtp
      tp' = aff2linTp tp
      (xtm', fvsx) = aff2linh g xtm
      (tm', fvs) = aff2linh (ctxtDeclTerm g x xtp') tm
      tm'' = if Map.member x fvs then tm' else discard g x xtp' tm'
  in
    (TmLet x xtm' xtp' tm'' tp', Map.union fvsx (Map.delete x fvs))
aff2linh g (TmCase tm y cs tp) =
  let csxs = map (aff2linCase g) cs
      xsAny = Map.unions (map snd csxs)
      (tm', tmxs) = aff2linh g tm
      cs' = flip map csxs $ \ (Case x as tm', xs) -> Case x as $
                  -- Need to discard any vars that occur free in other cases, but
                  -- not in this one bc all cases must have same set of free vars
                  discards (ctxtDeclArgs g as) (Map.difference xsAny xs) tm' in
    (TmCase tm' y cs' (aff2linTp tp), Map.union xsAny tmxs)
aff2linh g (TmSamp d tp) = (TmSamp d (aff2linTp tp), Map.empty)
aff2linh g (TmFold fuf tm tp) =
  let (tm', fvs) = aff2linh g tm in
    (TmFold fuf tm' (aff2linTp tp), fvs)

-- Makes an affine term linear
aff2linTerm :: Ctxt -> Term -> Term
aff2linTerm g tm =
  let (tm', fvs) = aff2linh g tm in
    if Map.null fvs
      then tm'
      else error ("in aff2lin, remaining free vars: " ++ show (Map.keys fvs))

-- Make an affine Prog linear
aff2linProg :: Ctxt -> Prog -> Prog
aff2linProg g (ProgFun x tp tm) =
  ProgFun x (aff2linTp tp) (aff2linTerm g tm)
aff2linProg g (ProgExtern x xp tp) =
  ProgExtern x xp (aff2linTp tp)
aff2linProg g (ProgData y cs) =
  ProgData y (map (\ (Ctor x as) -> Ctor x (map aff2linTp as)) cs)

-- Make an affine file linear
aff2linFile :: Progs -> Progs
aff2linFile (Progs ps end) =
  let g = ctxtDefProgs (Progs ps end) in
    Progs (map (aff2linProg g) ps) (aff2linTerm g end)




-- Records an instantiation of a polymorphic type
piAppend :: Var -> [Type] -> Map.Map Var [[Type]] -> Map.Map Var [[Type]]
piAppend y tp pis = Map.insertWith (++) y [tp] pis

-- Retrieves all instantiations of polymorphic types (e.g. Maybe [...]) in a term
getPolyInstsTerm :: Map.Map Var [[Type]] -> Term -> Map.Map Var [[Type]]
getPolyInstsTerm pis (TmVarL x tp) = getPolyInstsType pis tp
getPolyInstsTerm pis (TmVarG gv x as tp) = foldl (\ pis (a, atp) -> getPolyInstsTerm pis a) (getPolyInstsType pis tp) as
getPolyInstsTerm pis (TmLam x tp tm tp') = getPolyInstsTerm (getPolyInstsType pis tp) tm -- no need to do tp' bc tm already adds all insts
getPolyInstsTerm pis (TmApp tm1 tm2 tp2 tp) = getPolyInstsTerm (getPolyInstsTerm pis tm2) tm1
getPolyInstsTerm pis (TmLet x xtm xtp tm tp) = getPolyInstsTerm (getPolyInstsTerm pis xtm) tm
getPolyInstsTerm pis (TmCase tm y cs tp) =
  foldl (\ pis (Case x as ctm) -> getPolyInstsTerm pis ctm)
    (getPolyInstsType (getPolyInstsTerm pis tm) y) cs
getPolyInstsTerm pis (TmSamp d tp) = getPolyInstsType pis tp
getPolyInstsTerm pis (TmFold fuf tm tp) = getPolyInstsTerm pis tm

-- Retrives all instantiations of polymorphic types (e.g. Maybe [...]) in a type
getPolyInstsType :: Map.Map Var [[Type]] -> Type -> Map.Map Var [[Type]]
getPolyInstsType pis (TpVar y) = pis
getPolyInstsType pis (TpArr tp1 tp2) = getPolyInstsType (getPolyInstsType pis tp1) tp2
getPolyInstsType pis TpBool = piAppend tpBoolName [] pis
getPolyInstsType pis (TpMaybe tp) = piAppend tpMaybeName [tp] (getPolyInstsType pis tp)

-- Retrives all instantiations of polymorphic types (e.g. Maybe [...]) in a Prog
getPolyInstsProg :: Map.Map Var [[Type]] -> Prog -> Map.Map Var [[Type]]
getPolyInstsProg pis (ProgFun x tp tm) = getPolyInstsTerm pis tm
getPolyInstsProg pis (ProgExtern x xp tp) = getPolyInstsType pis tp
getPolyInstsProg pis (ProgData y cs) = foldl (\ pis (Ctor x as) -> foldl getPolyInstsType pis as) pis cs

getPolyInstsProgs :: Map.Map Var [[Type]] -> Progs -> Map.Map Var [[Type]]
getPolyInstsProgs pis (Progs ps tm) = Map.unionsWith (++) (getPolyInstsTerm pis tm : map (getPolyInstsProg pis) ps)

-- Retrives all instantiations of a particular polymorphic type var (e.g. Maybe [...])
getPolyInsts :: Progs -> Var -> [[Type]]
getPolyInsts ps y =
  let is = getPolyInstsProgs Map.empty ps in
    maybe [] nub (Map.lookup y is)
