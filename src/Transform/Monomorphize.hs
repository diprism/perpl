{- Takes a schemified (polymorphic) program and monomorphizes it -}

module Transform.Monomorphize where
import Struct.Lib
import Util.Helpers
import Scope.Subst (Subst(tags, tpVars), subst)
import Scope.Name (instTmName, instTpName)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- m1 <> m2 applies (<>) to the shared members of
-- the maps instead of just using m1's, as the default Semigroup instance of Map does
newtype Semimap a b = Semimap (Map a b) deriving Show
instance (Ord a, Semigroup b) => Semigroup (Semimap a b) where
  Semimap lm1 <> Semimap lm2 = Semimap (Map.unionWith (<>) lm1 lm2)
instance (Ord a, Semigroup b) => Monoid (Semimap a b) where
  mempty = Semimap mempty
-- Extract the map part of a semimap
semimap :: Semimap a b -> Map a b
semimap (Semimap m) = m

-- A global name
data Var = TmName TmName | TpName TpName deriving (Eq, Ord, Show)
-- Maps a definition name to the instantiations it has
-- (where each inst is a list of types, one for each tag/type var)
type Insts = Semimap Var (Set.Set ([Tag], [Type]))
-- Map a definition to the tag and type vars it is polymorphic over
type TypeParams = Map Var ([Tag], [TpVar])
-- List of global calls something makes, and the instantiation of each call
type GlobalCalls = [(Var, [Tag], [Type])]
-- Maps a definition name to all the other defs it calls and how it instantiates them
type DefMap = Map Var GlobalCalls

-- Collects all the global calls in a term
collectCalls :: Term -> GlobalCalls
collectCalls tm = collectCalls' tm <> collectCallsTp (typeof tm)

collectCalls' :: Term -> GlobalCalls
collectCalls' (TmVarL x tp) =
  collectCallsTp tp
collectCalls' (TmVarG g x tgs tis as tp) =
  [(TmName x, tgs, tis)] <> mconcat (collectCalls <$> fsts as)
collectCalls' (TmLam x xtp tm tp) =
  collectCalls tm
collectCalls' (TmApp tm1 tm2 tp2 tp) =
  collectCalls tm1 <> collectCalls tm2
collectCalls' (TmLet x xtm xtp tm tp) =
  collectCalls xtm <> collectCalls tm
collectCalls' (TmCase tm y cs tp) =
  collectCalls tm <> mconcat (fmap (\ (Case x ps tm') -> collectCalls tm') cs)
collectCalls' (TmAmb tms tp) =
  mconcat (fmap collectCalls tms)
collectCalls' (TmFactorDouble wt tm tp) =
  collectCalls tm
collectCalls' (TmFactorNat wt tm tp) =
  collectCalls tm
collectCalls' (TmFactorRatio wt tm tp) =
  collectCalls tm
collectCalls' (TmProd am as) =
  mconcat (fmap (collectCalls . fst) as)
collectCalls' (TmElimMultiplicative ptm ps tm tp) =
  collectCalls ptm <> collectCalls tm
collectCalls' (TmElimAdditive ptm n i p tm tp) =
  collectCalls ptm <> collectCalls tm
collectCalls' (TmEqs tms) =
  mconcat (fmap collectCalls tms)

-- Collects datatype calls in a type
collectCallsTp :: Type -> GlobalCalls
collectCallsTp (TpData y tgs as) = [(TpName y, tgs, as)] <> mconcat (map collectCallsTp as)
collectCallsTp (TpArr tp1 tp2)   = collectCallsTp tp1 <> collectCallsTp tp2
collectCallsTp (TpProd am tps)   = mconcat (map collectCallsTp tps)
collectCallsTp (TpVar v)         = []
collectCallsTp NoTp              = []

-- Substitutes polymorphic calls for their monomorphized version
-- (So if we instantiate List with Bool and Unit, then `List1 = List Bool` and
--  `List2 = List Unit` (copy definition and substitute type param for instantiation),
--  and `reverse1 : List1 -> List1` and `reverse2 : List2 -> List2`; then, replace all
--  calls to `reverse` for a List Bool with `reverse1` and similarly for `reverse2`
--  with calls to List Unit)
renameCalls :: Map Var (Map ([Tag], [Type]) Int) -> Term -> Term
renameCalls xis (TmVarL x tp) = TmVarL x (renameCallsTp xis tp)
renameCalls xis (TmVarG g x [] [] as tp) = TmVarG g x [] [] [(renameCalls xis tm, renameCallsTp xis tp) | (tm, tp) <- as] (renameCallsTp xis tp)
renameCalls xis (TmVarG g x tgs tis as tp) =
  let xi = (xis Map.! TmName x) Map.! (tgs, tis) in
    TmVarG g (instTmName x xi) [] []
      [(renameCalls xis tm, renameCallsTp xis tp)| (tm, tp) <- as]
      (renameCallsTp xis tp)
renameCalls xis (TmLam x xtp tm tp) = TmLam x (renameCallsTp xis xtp) (renameCalls xis tm) (renameCallsTp xis tp)
renameCalls xis (TmApp tm1 tm2 tp2 tp) = TmApp (renameCalls xis tm1) (renameCalls xis tm2) (renameCallsTp xis tp2) (renameCallsTp xis tp)
renameCalls xis (TmLet x xtm xtp tm tp) = TmLet x (renameCalls xis xtm) (renameCallsTp xis xtp) (renameCalls xis tm) (renameCallsTp xis tp)
renameCalls xis (TmCase tm (y, tgs, as) cs tp) =
  let yi = (if null tgs && null as then Nothing else Just ()) >> xis Map.!? TpName y >>= \ m -> m Map.!? (tgs, as)
      (y', tgs', as') = maybe (y, tgs, as) (\ i -> (instTpName y i, [], [])) yi
  in
    TmCase (renameCalls xis tm) (y', tgs', as')
      (fmap (\ (Case x ps tm') -> Case (maybe x (instTmName x) yi) [(x', renameCallsTp xis tp) | (x', tp) <- ps] (renameCalls xis tm')) cs) (renameCallsTp xis tp)
renameCalls xis (TmAmb tms tp) = TmAmb (renameCalls xis <$> tms) (renameCallsTp xis tp)
renameCalls xis (TmFactorDouble wt tm tp) = TmFactorDouble wt (renameCalls xis tm) (renameCallsTp xis tp)
renameCalls xis (TmFactorNat wt tm tp) = TmFactorNat wt (renameCalls xis tm) (renameCallsTp xis tp)
renameCalls xis (TmFactorRatio wt tm tp) = TmFactorRatio wt (renameCalls xis tm) (renameCallsTp xis tp)
renameCalls xis (TmProd am as) = TmProd am [(renameCalls xis tm, renameCallsTp xis tp) | (tm, tp) <- as]
renameCalls xis (TmElimMultiplicative ptm ps tm tp) = TmElimMultiplicative (renameCalls xis ptm) [(x, renameCallsTp xis xtp) | (x, xtp) <- ps] (renameCalls xis tm) (renameCallsTp xis tp)
renameCalls xis (TmElimAdditive ptm n i (x,xtp) tm tp) = TmElimAdditive (renameCalls xis ptm) n i (x, renameCallsTp xis xtp) (renameCalls xis tm) (renameCallsTp xis tp)
renameCalls xis (TmEqs tms) = TmEqs (renameCalls xis <$> tms)

-- Same as renameCalls, but for types
renameCallsTp :: Map Var (Map ([Tag], [Type]) Int) -> Type -> Type
renameCallsTp xis (TpData y [] []) = TpData y [] [] -- a datatype with no arguments can have only one instantiation, so we don't rename it (see makeInstantiations))
renameCallsTp xis (TpData y tgs as) =
  maybe (TpData y tgs as)
    (\ m -> let yi = m Map.! (tgs, as) in TpData (instTpName y yi) [] [])
    (xis Map.!? TpName y)
renameCallsTp xis (TpArr tp1 tp2) = TpArr (renameCallsTp xis tp1) (renameCallsTp xis tp2)
renameCallsTp xis (TpProd am tps) = TpProd am (map (renameCallsTp xis) tps)
renameCallsTp xis (TpVar (TpV y)) = error ("renameCallsTp sees a TpVar " ++ show y)
renameCallsTp xis NoTp = NoTp

-- Set up a map with an empty entry ([]) for each definition
makeEmptyInsts :: [SProg] -> Insts
makeEmptyInsts = mconcat . map h where
  h (SProgDefine x tgs ys tm tp) = Semimap (Map.singleton (TmName x) mempty)
  h (SProgExtern x tp) = Semimap (Map.singleton (TmName x) mempty)
  h (SProgData y tgs ps cs) = Semimap (Map.fromList ((TpName y, mempty) : map (\ (Ctor x tps) -> (TmName x, mempty)) cs))

-- Set up def map with an entry for each definition that stores the calls
-- to other definitions and how it instantiates them
makeDefMap :: [SProg] -> DefMap
makeDefMap = semimap . mconcat . map h where  
  h (SProgDefine x tgs ys tm tp) = Semimap (Map.singleton (TmName x) (collectCalls tm))
  h (SProgExtern x tp) = Semimap (Map.singleton (TmName x) (collectCallsTp tp))
  h (SProgData y tgs ps cs) =
    let ccs = map (\ (Ctor x tps) -> (TmName x, mconcat (map collectCallsTp tps))) cs in
      Semimap (Map.fromList ((TpName y, mconcat (snds ccs)) : ccs))

-- Store the tag and type vars each definition is polymorphic over
makeTypeParams :: [SProg] -> TypeParams
makeTypeParams = mconcat . map h where
  h (SProgDefine x tgs ys tm tp) = Map.singleton (TmName x) (tgs, [y | Forall y r <- ys])
  h (SProgExtern x tp) = Map.singleton (TmName x) ([], [])
  h (SProgData y tgs ps cs) = Map.fromList ((TpName y, (tgs, ps)) : map (\ (Ctor x tps) -> (TmName x, (tgs, ps))) cs)

-- If not visited, insert into Insts and recurse
addInsts :: DefMap -> TypeParams -> Insts -> Var -> [Tag] -> [Type] -> Insts
addInsts dm tpms xis x tgs tis
  -- if already visited, or not polymorphic in the first place, just return xis
  | not (x `Map.member` semimap xis) || (tgs,tis) `Set.member` (semimap xis Map.! x) = xis
  | otherwise = processNext x dm tpms
                  (xis <> Semimap (Map.singleton x (Set.singleton (tgs,tis)))) x tgs tis
  where
    -- Depth-first traversal with cur as root
    processNext :: Var -> DefMap -> TypeParams -> Insts -> Var -> [Tag] -> [Type] -> Insts
    processNext cur dm tpms xis x tgs tis =
      let (curtgs, curpms) = tpms Map.! cur
          curtis = semimap xis Map.! cur
      in
        foldr (\ (x, tgs, tis) xis ->
                  foldr (\ (ctgs,ctis) xis ->
                           let s = mempty{tags = Map.fromList (pickyZip curtgs ctgs), tpVars = Map.fromList (pickyZip curpms ctis)} in
                            addInsts dm tpms xis x (subst s tgs) (subst s tis))
                        xis curtis)
              xis (dm Map.! x)

-- Given a map from def name to its instance names, duplicate a def for each instantation
makeInstantiations :: Map Var (Map ([Tag], [Type]) Int) -> SProg -> [Prog]
makeInstantiations xis (SProgDefine x [] [] tm tp) =
  if null (Map.toList (xis Map.! TmName x)) then
    -- if x is never instantiated even with [] (since it has no tags/type vars),
    -- then this def is never used so we can just delete it
    []
  else
    [ProgDefine x [] (renameCalls xis tm) (renameCallsTp xis tp)]
makeInstantiations xis (SProgDefine x tgs ps tm tp) =
  let tiss = Map.toList (xis Map.! TmName x)
      ps' = [y | Forall y r <- ps] in
    map (\ ((tgs', tis), i) ->
           let s = mempty{tags   = Map.fromList (pickyZip tgs tgs'),
                          tpVars = Map.fromList (pickyZip ps' tis )} in
             ProgDefine
               (instTmName x i) -- new name for this particular instantiation
               [] -- args are [], for now (see Transform.Argify)
               (renameCalls xis (subst s tm))
               (renameCallsTp xis (subst s tp)))
      tiss
makeInstantiations xis (SProgExtern x tp) =
  if null (Map.toList (xis Map.! TmName x)) then
    []
  else
    [ProgExtern x [] (renameCallsTp xis tp)] -- args are [], for now (see Transform.Argify)
makeInstantiations xis (SProgData y [] [] cs) =
  if null (Map.toList (xis Map.! TpName y)) then
    []
  else
    -- a datatype with no arguments can have only one instantiation, so we don't rename it (see renameCallsTp)
    [ProgData y [Ctor x (map (renameCallsTp xis) tps) | Ctor x tps <- cs]]
makeInstantiations xis (SProgData y tgs ps cs) =
    let tiss = Map.toList (xis Map.! TpName y) in
    map (\ ((tags, tis), i) ->
           let s = mempty{tags   = Map.fromList (pickyZip tgs tags),
                          tpVars = Map.fromList (pickyZip ps  tis )} in
             ProgData
               (instTpName y i) -- new name for this particular instantiation
               [Ctor (instTmName x i) (map (renameCallsTp xis) (subst s tps))
               | Ctor x tps <- cs])
      tiss


-- See issue #59.
-- Overrides constructor instantiations, setting them to the instantiations
-- of their datatype. This avoids generating mismatched/confusing datatypes
-- and constructors like:
--   data Nat_inst0 = Zero_inst5 | Succ_inst2
overrideCtorInsts :: Map Var (Map ([Tag], [Type]) Int) -> [SProg] -> Map Var (Map ([Tag], [Type]) Int)
overrideCtorInsts m [] = m
overrideCtorInsts m (SProgData y tgs pms cs : sps) =
  let yis = m Map.! TpName y
      m' = foldr (\ (Ctor x _) -> Map.insert (TmName x) yis) m cs in
    overrideCtorInsts m' sps
overrideCtorInsts m (_ : sps) = overrideCtorInsts m sps

-- Duplicates polymorphic defs for each instantiation they have,
-- returning a monomorphic program
monomorphizeFile :: SProgs -> Progs
monomorphizeFile (SProgs sps stm) =
  let dm = makeDefMap sps
      tpms = makeTypeParams sps
      xis = makeEmptyInsts sps
      xis' = foldr (\ (x, tgs, tis) xis -> addInsts dm tpms xis x tgs tis) xis (collectCalls stm)
      xis'' = fmap (\ tiss -> Map.fromList (zip (Set.toList tiss) [0..])) (semimap xis')
      xis''' = overrideCtorInsts xis'' sps
  in
    Progs (concat (makeInstantiations xis''' <$> sps)) (renameCalls xis''' stm)
