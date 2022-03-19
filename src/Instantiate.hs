module Instantiate where
import Exprs
import Util
import Subst
import qualified Data.Map as Map
import qualified Data.Set as Set

newtype SemiMap a b = SemiMap (Map.Map a b)
instance (Ord a, Semigroup b) => Semigroup (SemiMap a b) where
  SemiMap lm1 <> SemiMap lm2 = SemiMap (Map.unionWith (<>) lm1 lm2)
instance (Ord a, Semigroup b) => Monoid (SemiMap a b) where
  mempty = SemiMap mempty
semiMap :: SemiMap a b -> Map.Map a b
semiMap (SemiMap m) = m

type Insts = SemiMap Var (Set.Set [Type])
type GlobalCalls = [(Var, [Type])]
type TypeParams = Map.Map Var [Var]
type DefMap = Map.Map Var GlobalCalls
  
collectCalls :: Term -> GlobalCalls
collectCalls (TmVarL x tp) = []
collectCalls (TmVarG g x tis as tp) = [(x, tis)]
collectCalls (TmLam x xtp tm tp) = collectCalls tm
collectCalls (TmApp tm1 tm2 tp2 tp) = collectCalls tm1 <> collectCalls tm2
collectCalls (TmLet x xtm xtp tm tp) = collectCalls xtm <> collectCalls tm
collectCalls (TmCase tm y cs tp) = collectCalls tm <> mconcat (fmap (\ (Case x ps tm') -> collectCalls tm') cs)
collectCalls (TmSamp d tp) = []
collectCalls (TmAmb tms tp) = mconcat (fmap collectCalls tms)
collectCalls (TmProd am as) = mconcat (fmap (collectCalls . fst) as)
collectCalls (TmElimProd am ptm ps tm tp) = collectCalls ptm <> collectCalls tm
collectCalls (TmEqs tms) = mconcat (fmap collectCalls tms)

renameCalls :: Map.Map Var (Map.Map [Type] Int) -> Term -> Term
renameCalls xis (TmVarL x tp) = TmVarL x tp
renameCalls xis (TmVarG g x tis as tp) = error "TODO"
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
  h (SProgExtern x tps rtp) = mempty
  h (SProgData y cs) = mempty

makeDefMap :: [SProg] -> DefMap
makeDefMap = semiMap . mconcat . map h where
  h (SProgFun x (Forall ys tp) tm) = SemiMap (Map.singleton x (collectCalls tm))
  h (SProgExtern x tps rtp) = mempty
  h (SProgData y cs) = mempty

makeTypeParams :: [SProg] -> TypeParams
makeTypeParams = mconcat . map h where
  h (SProgFun x (Forall ys tp) tm) = Map.singleton x ys
  h (SProgExtern x tps rtp) = mempty
  h (SProgData y cs) = mempty

-- If not visited, insert into Insts and recurse
addInsts :: DefMap -> TypeParams -> Insts -> Var -> [Type] -> Insts
addInsts dm tpms xis x tis =
  if tis `Set.member` (semiMap xis Map.! x) then
    xis
  else
    processNext x dm tpms
      (xis <> SemiMap (Map.singleton x (Set.singleton tis))) x tis

-- If in start term, give "" for cur
-- TODO: Make sure no infinite loops, i.e. foo x = foo (x, unit) (or would this get caught during type-checking?)
processNext :: Var -> DefMap -> TypeParams -> Insts -> Var -> [Type] -> Insts
processNext "" dm tpms xis x tis =
  addInsts dm tpms xis x tis
processNext cur dm tpms xis x tis =
  let curpms = tpms Map.! cur
      curtis = semiMap xis Map.! cur
      tis' = Set.map (\ ctis -> subst (Map.fromList (zip curpms (SubTp <$> ctis))) tis) curtis
      tis'' = Set.toList tis' in
    foldr (\ tis xis -> addInsts dm tpms xis x tis) xis tis''

makeInstantiations :: Map.Map Var (Map.Map [Type] Int) -> SProg -> [Prog]
makeInstantiations xis (SProgFun x (Forall ys tp) tm) =
  map (\ (tis, i) -> let s = Map.fromList (zip ys (SubTp <$> tis)) in
                       ProgFun x [] (renameCalls xis (subst s tm)) (subst s tp))
      (Map.toList (xis Map.! x))
makeInstantiations xis (SProgExtern x tps rtp) = [ProgExtern x "" tps rtp] -- TODO: string ""?
makeInstantiations xis (SProgData y cs) = [ProgData y cs]

instantiate :: SProgs -> Progs
instantiate (SProgs sps stm) =
  let dm = makeDefMap sps
      tpms = makeTypeParams sps
      xis = makeEmptyInsts sps
      xis' = foldr (\ (x, tis) xis -> addInsts dm tpms xis x tis) xis (collectCalls stm)
      xis'' = fmap (\ tiss -> Map.fromList (zip (Set.toList tiss) [0..])) (semiMap xis')
  in
    Progs (concat (makeInstantiations xis'' <$> sps)) (renameCalls xis'' stm)
