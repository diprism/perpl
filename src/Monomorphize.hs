module Monomorphize where
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
type TypeParams = Map Var ([Var], [Var])
type DefMap = Map Var GlobalCalls
  
collectCalls :: Term -> GlobalCalls
collectCalls tm = collectCalls' tm <> collectCallsTp (typeof tm)

collectCalls' :: Term -> GlobalCalls
collectCalls' (TmVarL x tp) = collectCallsTp tp
collectCalls' (TmVarG g x tis as tp) = [(x, tis)] <> mconcat (collectCalls <$> fsts as)
collectCalls' (TmLam x xtp tm tp) = collectCalls tm
collectCalls' (TmApp tm1 tm2 tp2 tp) = collectCalls tm1 <> collectCalls tm2
collectCalls' (TmLet x xtm xtp tm tp) = collectCalls xtm <> collectCalls tm
collectCalls' (TmCase tm y cs tp) = collectCalls tm <> mconcat (fmap (\ (Case x ps tm') -> collectCalls tm') cs)
collectCalls' (TmSamp d tp) = []
collectCalls' (TmAmb tms tp) = mconcat (fmap collectCalls tms)
collectCalls' (TmProd am as) = mconcat (fmap (collectCalls . fst) as)
collectCalls' (TmElimProd am ptm ps tm tp) = collectCalls ptm <> collectCalls tm
collectCalls' (TmEqs tms) = mconcat (fmap collectCalls tms)

collectCallsTp :: Type -> GlobalCalls
collectCallsTp (TpVar y as) = [(y, as)]
collectCallsTp (TpArr tp1 tp2) = collectCallsTp tp1 <> collectCallsTp tp2
collectCallsTp (TpProd am tps) = mconcat (map collectCallsTp tps)
collectCallsTp NoTp = []

renameCalls :: Map Var (Map [Type] Int) -> Term -> Term
renameCalls xis (TmVarL x tp) = TmVarL x (renameCallsTp xis tp)
renameCalls xis (TmVarG g x [] as tp) = TmVarG g x [] [(renameCalls xis tm, renameCallsTp xis tp)| (tm, tp) <- as] (renameCallsTp xis tp)
renameCalls xis (TmVarG g x tis as tp) =
  let xisx = xis Map.! x
      xi = (xis Map.! x) Map.! tis in
    TmVarG g (instName x xi) []
      [(renameCalls xis tm, renameCallsTp xis tp)| (tm, tp) <- as]
      (renameCallsTp xis tp)
renameCalls xis (TmLam x xtp tm tp) = TmLam x (renameCallsTp xis xtp) (renameCalls xis tm) (renameCallsTp xis tp)
renameCalls xis (TmApp tm1 tm2 tp2 tp) = TmApp (renameCalls xis tm1) (renameCalls xis tm2) (renameCallsTp xis tp2) (renameCallsTp xis tp)
renameCalls xis (TmLet x xtm xtp tm tp) = TmLet x (renameCalls xis xtm) (renameCallsTp xis xtp) (renameCalls xis tm) (renameCallsTp xis tp)
renameCalls xis (TmCase tm (y, as) cs tp) =
  let yi = (if null as then Nothing else Just ()) >> xis Map.!? y >>= \ m -> m Map.!? as
      (y', as') = maybe (y, as) (\ i -> (instName y i, [])) yi in
--      (y', as') = maybe (y, as) (\ m -> let yi = maybe (error $ "y = " ++ y ++ ", as = " ++ show as ++ ", xis = " ++ show xis) id (m Map.!? as) in (instName y yi, [])) (xis Map.!? y) in
    TmCase (renameCalls xis tm) (y', as')
      (fmap (\ (Case x ps tm') -> Case (maybe x (instName x) yi) [(x', renameCallsTp xis tp) | (x', tp) <- ps] (renameCalls xis tm')) cs) (renameCallsTp xis tp)
renameCalls xis (TmSamp d tp) = TmSamp d (renameCallsTp xis tp)
renameCalls xis (TmAmb tms tp) = TmAmb (renameCalls xis <$> tms) (renameCallsTp xis tp)
renameCalls xis (TmProd am as) = TmProd am [(renameCalls xis tm, renameCallsTp xis tp) | (tm, tp) <- as]
renameCalls xis (TmElimProd am ptm ps tm tp) = TmElimProd am (renameCalls xis ptm) [(x, renameCallsTp xis tp) | (x, tp) <- ps] (renameCalls xis tm) (renameCallsTp xis tp)
renameCalls xis (TmEqs tms) = TmEqs (renameCalls xis <$> tms)

renameCallsTp :: Map Var (Map [Type] Int) -> Type -> Type
renameCallsTp xis (TpVar y []) = TpVar y []
renameCallsTp xis (TpVar y as) =
  maybe (TpVar y as)
    (\ m -> let yi = m Map.! as in TpVar (instName y yi) [])
    (xis Map.!? y)
renameCallsTp xis (TpArr tp1 tp2) = TpArr (renameCallsTp xis tp1) (renameCallsTp xis tp2)
renameCallsTp xis (TpProd am tps) = TpProd am (map (renameCallsTp xis) tps)
renameCallsTp xis NoTp = NoTp

makeEmptyInsts :: [SProg] -> Insts
makeEmptyInsts = mconcat . map h where
  h (SProgFun x (Forall tgs ys tp) tm) = SemiMap (Map.singleton x mempty)
  h (SProgExtern x tps rtp) = SemiMap (Map.singleton x mempty)
  h (SProgData y tgs ps cs) = SemiMap (Map.fromList ((y, mempty) : map (\ (Ctor x tps) -> (x, mempty)) cs))

makeDefMap :: [SProg] -> DefMap
makeDefMap = semiMap . mconcat . map h where
--  clean :: DefMap -> DefMap
--  clean dm = fmap (\ gcs -> Map.toList (Map.intersection (Map.fromList gcs) dm)) dm
  
  h (SProgFun x (Forall tgs ys tp) tm) = SemiMap (Map.singleton x (collectCalls tm))
  h (SProgExtern x tps rtp) = SemiMap (Map.singleton x [])
  h (SProgData y tgs ps cs) =
    let ccs = map (\ (Ctor x tps) -> (x, mconcat (map collectCallsTp tps))) cs in
      SemiMap (Map.fromList ((y, mconcat (snds ccs)) : ccs))

makeTypeParams :: [SProg] -> TypeParams
makeTypeParams = mconcat . map h where
  h (SProgFun x (Forall tgs ys tp) tm) = Map.singleton x (tgs, ys)
  h (SProgExtern x tps rtp) = Map.singleton x ([], [])
  h (SProgData y tgs ps cs) = Map.fromList ((y, (tgs, ps)) : map (\ (Ctor x tps) -> (x, (tgs, ps))) cs)

-- If not visited, insert into Insts and recurse
addInsts :: DefMap -> TypeParams -> Insts -> Var -> [Type] -> Insts
addInsts dm tpms xis x tis =
  if not (x `Map.member` semiMap xis) || tis `Set.member` (semiMap xis Map.! x) then
    xis
  else
    processNext x dm tpms
      (xis <> SemiMap (Map.singleton x (Set.singleton tis))) x tis

processNext :: Var -> DefMap -> TypeParams -> Insts -> Var -> [Type] -> Insts
processNext cur dm tpms xis x tis =
  let (curtgs, curpms) = tpms Map.! cur
      curtis = semiMap xis Map.! cur
      mksub = \ ctis -> Map.fromList (zip (curtgs ++ curpms) (SubTp <$> ctis)) in
    foldr (\ (x, tis) xis -> foldr (\ ctis xis -> addInsts dm tpms xis x (subst (mksub ctis) tis)) xis curtis) xis (dm Map.! x)

makeInstantiations :: Map Var (Map [Type] Int) -> SProg -> [Prog]
makeInstantiations xis (SProgFun x (Forall [] [] tp) tm) =
  if null (Map.toList (xis Map.! x)) then [] else [ProgFun x [] (renameCalls xis tm) (renameCallsTp xis tp)]
makeInstantiations xis (SProgFun x (Forall tgs ys tp) tm) =
  let tiss = Map.toList (xis Map.! x) in
    map (\ (tis, i) ->
           let s = Map.fromList (zip (tgs ++ ys) (SubTp <$> tis)) in
             ProgFun (instName x i) [] (renameCalls xis (subst s tm)) (renameCallsTp xis (subst s tp)))
      tiss
makeInstantiations xis (SProgExtern x tps rtp) = [ProgExtern x tps rtp]
makeInstantiations xis (SProgData y [] [] cs) = [ProgData y cs]
makeInstantiations xis (SProgData y tgs ps cs) =
    let tiss = Map.toList (xis Map.! y) in
    map (\ (tis, i) ->
           let s = Map.fromList (zip (tgs ++ ps) (SubTp <$> tis)) in
             ProgData (instName y i) [Ctor (instName x i) (map (renameCallsTp xis) (subst s tps)) | Ctor x tps <- cs])
      tiss

monomorphizeFile :: SProgs -> Progs
monomorphizeFile (SProgs sps stm) =
  let dm = makeDefMap sps
      tpms = makeTypeParams sps
      xis = makeEmptyInsts sps
      xis' = foldr (\ (x, tis) xis -> addInsts dm tpms xis x tis) xis (collectCalls stm)
      xis'' = fmap (\ tiss -> Map.fromList (zip (Set.toList tiss) [0..])) (semiMap xis')
  in
    Progs (concat (makeInstantiations xis'' <$> sps)) (renameCalls xis'' stm)
