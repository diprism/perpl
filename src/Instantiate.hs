module Instantiate where
import Exprs
import Util
import Subst
import Name
import qualified Data.Map as Map
import qualified Data.Set as Set

newtype SemiMap a b = SemiMap (Map a b) deriving Show
instance (Ord a, Semigroup b) => Semigroup (SemiMap a b) where
  SemiMap lm1 <> SemiMap lm2 = SemiMap (Map.unionWith (<>) lm1 lm2)
instance (Ord a, Semigroup b) => Monoid (SemiMap a b) where
  mempty = SemiMap mempty
semiMap :: SemiMap a b -> Map a b
semiMap (SemiMap m) = m

type Insts = SemiMap Var (Set.Set [Type])
type GlobalCalls = [(Var, [Type])]
type TypeParams = Map Var [Var]
type DefMap = Map Var GlobalCalls
  
collectCalls :: Term -> GlobalCalls
collectCalls (TmVarL x tp) = []
collectCalls (TmVarG g x tis as tp) = [(x, tis)] <> mconcat (collectCalls <$> fsts as)
collectCalls (TmLam x xtp tm tp) = collectCalls tm
collectCalls (TmApp tm1 tm2 tp2 tp) = collectCalls tm1 <> collectCalls tm2
collectCalls (TmLet x xtm xtp tm tp) = collectCalls xtm <> collectCalls tm
collectCalls (TmCase tm y cs tp) = collectCalls tm <> mconcat (fmap (\ (Case x ps tm') -> collectCalls tm') cs)
collectCalls (TmSamp d tp) = []
collectCalls (TmAmb tms tp) = mconcat (fmap collectCalls tms)
collectCalls (TmProd am as) = mconcat (fmap (collectCalls . fst) as)
collectCalls (TmElimProd am ptm ps tm tp) = collectCalls ptm <> collectCalls tm
collectCalls (TmEqs tms) = mconcat (fmap collectCalls tms)

renameCalls :: Map Var (Map [Type] Int) -> Term -> Term
renameCalls xis (TmVarL x tp) = TmVarL x tp
renameCalls xis (TmVarG g x [] as tp) = TmVarG g x [] [(renameCalls xis tm, tp)| (tm, tp) <- as] tp
renameCalls xis (TmVarG g x tis as tp) =
  let xisx = xis Map.! x
      xi = (xis Map.! x) Map.! tis in
    if Map.member tis xisx then
      TmVarG g (instName x xi) [] [(renameCalls xis tm, tp)| (tm, tp) <- as] tp
    else error ("renameCalls: " ++ x ++ " " ++ show tis ++ " " ++ show xis)
renameCalls xis (TmLam x xtp tm tp) = TmLam x xtp (renameCalls xis tm) tp
renameCalls xis (TmApp tm1 tm2 tp2 tp) = TmApp (renameCalls xis tm1) (renameCalls xis tm2) tp2 tp
renameCalls xis (TmLet x xtm xtp tm tp) = TmLet x (renameCalls xis xtm) xtp (renameCalls xis tm) tp
renameCalls xis (TmCase tm y cs tp) = TmCase (renameCalls xis tm) y (fmap (\ (Case x ps tm') -> Case x ps (renameCalls xis tm')) cs) tp
renameCalls xis (TmSamp d tp) = TmSamp d tp
renameCalls xis (TmAmb tms tp) = TmAmb (renameCalls xis <$> tms) tp
renameCalls xis (TmProd am as) = TmProd am [(renameCalls xis tm, tp) | (tm, tp) <- as]
renameCalls xis (TmElimProd am ptm ps tm tp) = TmElimProd am (renameCalls xis ptm) ps (renameCalls xis tm) tp
renameCalls xis (TmEqs tms) = TmEqs (renameCalls xis <$> tms)

makeEmptyInsts :: [SProg] -> Insts
makeEmptyInsts = mconcat . map h where
  h (SProgFun x (Forall ys tp) tm) = SemiMap (Map.singleton x mempty)
  h (SProgExtern x tps rtp) = SemiMap (Map.singleton x mempty)
  h (SProgData y cs) = SemiMap (Map.fromList (map (\ (Ctor x tps) -> (x, mempty)) cs))

makeDefMap :: [SProg] -> DefMap
makeDefMap = semiMap . mconcat . map h where
--  clean :: DefMap -> DefMap
--  clean dm = fmap (\ gcs -> Map.toList (Map.intersection (Map.fromList gcs) dm)) dm
  
  h (SProgFun x (Forall ys tp) tm) = SemiMap (Map.singleton x (collectCalls tm))
  h (SProgExtern x tps rtp) = SemiMap (Map.singleton x [])
  h (SProgData y cs) = SemiMap (Map.fromList (map (\ (Ctor x tps) -> (x, [])) cs))

makeTypeParams :: [SProg] -> TypeParams
makeTypeParams = mconcat . map h where
  h (SProgFun x (Forall ys tp) tm) = Map.singleton x ys
  h (SProgExtern x tps rtp) = Map.singleton x []
  h (SProgData y cs) = Map.fromList (map (\ (Ctor x tps) -> (x, [])) cs)

-- If not visited, insert into Insts and recurse
addInsts :: DefMap -> TypeParams -> Insts -> Var -> [Type] -> Insts
addInsts dm tpms xis x tis =
  if tis `Set.member` (semiMap xis Map.! x) then
    xis
  else
    processNext x dm tpms
      (xis <> SemiMap (Map.singleton x (Set.singleton tis))) x tis

-- TODO: Make sure no infinite loops, i.e. foo x = foo (x, unit) (or would this get caught during type-checking?)
processNext :: Var -> DefMap -> TypeParams -> Insts -> Var -> [Type] -> Insts
processNext cur dm tpms xis x tis =
  let curpms = tpms Map.! cur
      curtis = semiMap xis Map.! cur
      mksub = \ ctis -> Map.fromList (zip curpms (SubTp <$> ctis)) in
    foldr (\ (x, tis) xis -> foldr (\ ctis xis -> addInsts dm tpms xis x (subst (mksub ctis) tis)) xis curtis) xis (dm Map.! x)

makeInstantiations :: Map Var (Map [Type] Int) -> SProg -> [Prog]
makeInstantiations xis (SProgFun x (Forall [] tp) tm) = [ProgFun x [] (renameCalls xis tm) tp]
makeInstantiations xis (SProgFun x (Forall ys tp) tm) =
  map (\ (tis, i) -> let s = Map.fromList (zip ys (SubTp <$> tis)) in
                       ProgFun (instName x i) [] (renameCalls xis (subst s tm)) (subst s tp))
      (Map.toList (xis Map.! x))
makeInstantiations xis (SProgExtern x tps rtp) = [ProgExtern x "" tps rtp] -- TODO: string ""?
makeInstantiations xis (SProgData y cs) = [ProgData y cs]

instantiateFile :: SProgs -> Progs
instantiateFile (SProgs sps stm) =
  let dm = makeDefMap sps
      tpms = makeTypeParams sps
      xis = makeEmptyInsts sps
      xis' = foldr (\ (x, tis) xis -> addInsts dm tpms xis x tis) xis (collectCalls stm)
      xis'' = fmap (\ tiss -> Map.fromList (zip (Set.toList tiss) [0..])) (semiMap xis')
  in
--    error ("dm: " ++ show dm ++ "\ntpms: " ++ show tpms ++ "\nxis'': " ++ show xis' ++ "\n")
    nicifyProgs (Progs (concat (makeInstantiations xis'' <$> sps)) (renameCalls xis'' stm))

nicify :: Term -> Term
nicify (TmVarL x tp) = TmVarL x tp
nicify (TmVarG g x _ _ tp) = TmVarG g x [] [] tp
nicify (TmLam x xtp tm tp) = TmLam x xtp (nicify tm) tp
nicify tm@(TmApp _ _ _ _) =
  case splitApps tm of
    (TmVarG g x _ _ tp , as) ->
      let (tps, etp) = splitArrows tp
          remtps = drop (length as) tps
          tmfvs = Map.mapWithKey (const . SubVar) (freeVars tm)
          lxs = runSubst tmfvs (freshens ["x" | _ <- [0..length remtps]])
          ls = zip lxs remtps
          as' = as ++ [(TmVarL x tp, tp) | (x, tp) <- ls]
      in
        joinLams ls (TmVarG g x [] as' etp)
    (etm, as) ->
      joinApps etm [(nicify tm, tp) | (tm, tp) <- as]
nicify (TmLet x xtm xtp tm tp) = TmLet x (nicify xtm) xtp (nicify tm) tp
nicify (TmCase tm y cs tp) = TmCase (nicify tm) y (fmap (\ (Case x ps tm') -> Case x ps (nicify tm')) cs) tp
nicify (TmSamp d tp) = TmSamp d tp
nicify (TmAmb tms tp) = TmAmb (nicify <$> tms) tp
nicify (TmProd am as) = TmProd am [(nicify tm, tp) | (tm, tp) <- as]
nicify (TmElimProd am ptm ps tm tp) = TmElimProd am (nicify ptm) ps (nicify tm) tp
nicify (TmEqs tms) = TmEqs (nicify <$> tms)

nicifyProg :: Prog -> Prog
nicifyProg (ProgFun x [] tm tp) =
  let tm' = nicify tm
      (tps, etp) = splitArrows tp
      (ls, etm) = splitLams tm'
      tp' = joinArrows (drop (length ls) tps) etp
  in
    ProgFun x ls etm tp'
nicifyProg (ProgExtern x xp [] tp) =
  let (tps, etp) = splitArrows tp in
    ProgExtern x xp tps etp
nicifyProg (ProgData y cs) = ProgData y cs
nicifyProg _ = error "This shouldn't happen"


nicifyProgs :: Progs -> Progs
nicifyProgs (Progs ps tm) = Progs (map nicifyProg ps) (nicify tm)
