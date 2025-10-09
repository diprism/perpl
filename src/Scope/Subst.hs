-- Adapted from http://dev.stephendiehl.com/fun/006_hindley_milner.html
{- Substitution code -}

module Scope.Subst (Subst(..), FreeVars(..), STerm(..),
                    Substitutable,
                    substM, subst, substWithCtxt, alphaRename,
                    substTags, substDatatype, freeDatatypes,
                    freeVars, FreeTmVars, freeVarLs) where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.String (IsString)
import Data.Maybe (fromMaybe)
import Data.Monoid (Endo(Endo, appEndo))
import Control.Monad.RWS.Lazy
import Struct.Exprs
import Util.Helpers
import Scope.Ctxt (Ctxt)
import qualified Scope.Ctxt as C
import Scope.Fresh (newVar, newVars)
import Struct.Lib

----------------------------------------

data STerm = Rename TmVar -- `Rename v` means `TmVarL v tp` where `tp` is unchanged
           | Replace Term
  deriving Show
data Subst = Subst { tmVars  :: Map TmVar STerm
                   , tpVars  :: Map TpVar Type
                   , tags    :: Map Tag   Tag
                   , tmNames :: Set TmName }
  deriving Show

instance Semigroup Subst where
  -- Composes two substitutions
  s1@(Subst m1 p1 g1 n1) <> s2@(Subst m2 p2 g2 n2) =
    Subst (Map.map (subst s1) m2 `Map.union` m1)
          (Map.map (subst s1) p2 `Map.union` p1)
          (Map.map (subst s1) g2 `Map.union` g1)
          (                   n2 `Set.union` n1)

instance Monoid Subst where
  mempty = Subst Map.empty Map.empty Map.empty Set.empty

-- State monad, where s = Subst
type SubstM = RWS () () Subst

{- The return type of freeVars. It maps from a variable x to its type if
   x is a term variable, and () otherwise.

   In UsTms, occurrences of global variables (UsVar x) are considered
   free, while in Terms, occurrences of global variables (TmVarG) are
   considered not free.

   Uses of datatype names (TpData x) are considered not free. -}

data FreeVars = FreeVars { freeTmVars :: Map TmVar Type
                         , freeTpVars :: Map TpVar ()
                         , freeTags   :: Map Tag () }
  deriving Show

instance Semigroup FreeVars where
  FreeVars m1 p1 g1 <> FreeVars m2 p2 g2 = FreeVars (m1 `Map.union` m2)
                                                    (p1 `Map.union` p2)
                                                    (g1 `Map.union` g2)

instance Monoid FreeVars where
  mempty = FreeVars Map.empty Map.empty Map.empty
  mconcat fvs = FreeVars (Map.unions (map freeTmVars fvs))
                         (Map.unions (map freeTpVars fvs))
                         (Map.unions (map freeTags   fvs))

-- Returns the free local variables of a Substitutable.
type FreeTmVars = Map TmVar Type
freeVarLs :: Substitutable a => a -> FreeTmVars
freeVarLs = freeTmVars . freeVars

-- Runs the substitution monad
runSubst :: Subst -> SubstM a -> a
runSubst s r = let (a', r', ()) = runRWS r () s in a'

class (Ord var, Show var, IsString var) => Var var where
  member :: var -> Subst -> Bool
  insert :: var -> var -> Subst -> (Subst, Subst -> Subst)

insertVar :: (Ord a, Show a) => a -> b -> b -> Map a b -> (Map a b, Map a b -> Map a b)
insertVar x x' y g = let (old, g') = Map.insertLookupWithKey (const const) x y g
                     in (g', Map.insert x (fromMaybe x' old))

instance Var TmVar where
  member   y g = y `Map.member` tmVars g || tmVarToName y `Set.member` tmNames g
  insert x y g = let (g', f) = insertVar x (Rename x) (Rename y) (tmVars g)
                 in (g{tmVars = g'}, \s -> s{tmVars = f (tmVars s)})

instance Var TpVar where
  member   y g = y `Map.member` tpVars g
  insert x y g = let (g', f) = insertVar x (TpVar x) (TpVar y) (tpVars g)
                 in (g{tpVars = g'}, \s -> s{tpVars = f (tpVars s)})

instance Var Tag where
  member   y g = y `Map.member` tags g
  insert x y g = let (g', f) = insertVar x x y (tags g)
                 in (g{tags = g'}, \s -> s{tags = f (tags s)})

-- Picks a name y, derived from x, that is fresh in the sense that it
-- is different from any variable in the current
-- substitution.
freshen :: (Var var) => var -> SubstM var
freshen x = state (\g -> let y = newVar x (`member` g)
                         in (y, fst (insert y y g)))

-- Pick fresh names (see freshen) for a list of vars
freshens :: (Var var) => [var] -> SubstM [var]
freshens xs = state (\g -> let ys = newVars xs (`member` g)
                           in (ys, foldr (\y -> fst . insert y y) g ys))

-- Rename x := y in m. Also performs the trivial substitution x :=
-- x, because any further α-conversions performed inside m need to
-- avoid both x and y.
bind :: (Var var) => var -> var -> SubstM a -> SubstM a
bind x y m = do
  f <- state (\g0 -> let (g1, f1) = insert x y g0
                         (g2, f2) = insert y y g1
                     in (f2 . f1, g2))
  a <- m
  modify f
  return a

-- Renames all xs to ys (see bind) in m
binds :: (Var var) => [var] -> [var] -> SubstM a -> SubstM a
binds xs ys m = foldr (uncurry bind) m (pickyZip xs ys)

-- Freshens param(s), and binds them in cont
substParam :: Param -> SubstM a -> SubstM (Param, a)
substParam (x, tp) cont =
  freshen x >>= \ x' ->
  substM tp >>= \ tp' ->
  bind x x' cont >>= \ a ->
  return ((x', tp'), a)
substParams :: [Param] -> SubstM a -> SubstM ([Param], a)
substParams [] cont = (,) [] <$> cont
substParams (p : ps) cont =
  substParam p (substParams ps cont) >>= \ ((x', tp'), (ps', a)) ->
  return ((x', tp') : ps', a)

-- "Substitutable" typeclass definition: must have freeVars and substM
class Substitutable a where
  freeVars :: a -> FreeVars
  substM :: a -> SubstM a

{- subst s a

Perform capture-avoiding substitution s on a Substitutable a.

It substitutes local variables (TmVars) and type variables (TpVars).
UsVars (whether they are local or global) are subject to Renames but not Replaces. -}
  
subst :: Substitutable a => Subst -> a -> a
subst s a = runSubst s (substM a)

-- Run substM under a given context
substWithCtxt :: Substitutable a => Ctxt -> Subst -> a -> a
substWithCtxt g = subst . remember (C.tmVars  g)
  where remember :: (Var var) => Map var val -> Subst -> Subst
        remember = appEndo . Map.foldMapWithKey (\x _ -> Endo (fst . insert x x))

-- Run substM with no substitutions, so just alpha-rename bound vars
alphaRename :: Substitutable a => Ctxt -> a -> a
alphaRename g = substWithCtxt g mempty{tmNames = Map.keysSet (C.tmNames g)}

-- Substitutes inside a Functor/Traversable t
substF :: (Functor t, Traversable t, Substitutable a) => t a -> SubstM (t a)
substF = mapM substM

-- Returns all free vars in a foldable
freeVarsF :: (Foldable f, Substitutable a) => f a -> FreeVars
freeVarsF = foldMap freeVars


instance Substitutable Type where
  substM (TpArr tp1 tp2) = pure TpArr <*> substM tp1 <*> substM tp2
  substM tp@(TpVar y) = fmap (Map.findWithDefault tp y . tpVars) get
  substM (TpData y tgs as) = pure (TpData y) <*> substM tgs <*> substM as
  substM (TpProd am tps) = pure (TpProd am) <*> substM tps
  substM NoTp = pure NoTp

  freeVars (TpArr tp1 tp2) = mappend (freeVars tp1) (freeVars tp2)
  freeVars (TpVar y) = mempty{freeTpVars = Map.singleton y ()}
  freeVars (TpData y tgs as) = freeVars tgs <> freeVars as
  freeVars (TpProd am tps) = mconcat (freeVars <$> tps)
  freeVars NoTp = mempty

instance Substitutable STerm where
  substM (Rename x) = fmap (Map.findWithDefault (Rename x) x . tmVars) get
  substM (Replace tm) = Replace <$> substM tm
  freeVars (Rename x) = mempty{freeTmVars = Map.singleton x NoTp}
  freeVars (Replace tm) = freeVars tm

instance Substitutable Term where
  substM (TmVarL x tp) =
    fmap (Map.findWithDefault (Rename x) x . tmVars) get >>= \rhs -> case rhs of
      Rename y -> pure (TmVarL y) <*> substM tp
      Replace t -> pure t
  substM (TmVarG g x tgs tis as tp) =
    pure (TmVarG g x) <*> substM tgs <*> substM tis <*> mapArgsM substM as <*> substM tp
  substM (TmLam x xtp tm tp) =
    freshen x >>= \ x' ->
    pure (TmLam x') <*> substM xtp <*> bind x x' (substM tm) <*> substM tp
  substM (TmApp tm1 tm2 tp2 tp) =
    pure TmApp <*> substM tm1 <*> substM tm2 <*> substM tp2 <*> substM tp
  substM (TmLet x xtm xtp tm tp) =
    freshen x >>= \ x' ->
    pure (TmLet x') <*> substM xtm <*> substM xtp <*> bind x x' (substM tm) <*> substM tp
  substM (TmCase tm (y, tgs, as) cs tp) =
    pure TmCase <*> substM tm <*> (pure ((,,) y) <*> substM tgs <*> substM as) <*> substM cs <*> substM tp
  substM (TmAmb tms tp) =
    pure TmAmb <*> substM tms <*> substM tp
  substM (TmFactorDouble wt tm tp) =
    pure TmFactorDouble <*> pure wt <*> substM tm <*> substM tp
  substM (TmFactorNat wt tm tp) =
    pure TmFactorNat <*> pure wt <*> substM tm <*> substM tp
  substM (TmFactorRatio wt tm tp) =
    pure TmFactorRatio <*> pure wt <*> substM tm <*> substM tp
  substM (TmProd am as) =
    pure (TmProd am) <*> mapArgsM substM as
  substM (TmElimAdditive ptm n i p tm tp) =
    pure TmElimAdditive <*> substM ptm <*> pure n <*> pure i <**> substParam p (substM tm) <*> substM tp
  substM (TmElimMultiplicative ptm ps tm tp) =
    pure TmElimMultiplicative <*> substM ptm <**> substParams ps (substM tm) <*> substM tp
  substM (TmEqs tms) =
    pure TmEqs <*> substM tms
  
  freeVars (TmVarL x tp) = mempty{freeTmVars = Map.singleton x tp}
  freeVars (TmVarG g x tgs tis as tp) = freeVars tgs <> freeVars tis <> freeVars (fsts as)
  freeVars (TmLam x xtp tm tp) = let fv = freeVars tm in fv{freeTmVars = Map.delete x (freeTmVars fv)}
  freeVars (TmApp tm1 tm2 tp2 tp) = freeVars tm1 <> freeVars tm2
  freeVars (TmLet x xtm xtp tm tp) = freeVars xtm <> let fv = freeVars tm in fv{freeTmVars = Map.delete x (freeTmVars fv)}
  freeVars (TmCase tm y cs tp) = freeVars tm <> freeVars cs
  freeVars (TmAmb tms tp) = freeVars tms
  freeVars (TmFactorDouble wt tm tp) = freeVars tm
  freeVars (TmFactorNat wt tm tp) = freeVars tm
  freeVars (TmFactorRatio wt tm tp) = freeVars tm
  freeVars (TmProd am as) = freeVars (fsts as)
  freeVars (TmElimAdditive ptm n i p tm tp) = freeVars ptm <> let fv = freeVars tm in fv{freeTmVars = Map.delete (fst p) (freeTmVars fv)}
  freeVars (TmElimMultiplicative ptm ps tm tp) = freeVars ptm <> let fv = freeVars tm in fv{freeTmVars = foldr (Map.delete . fst) (freeTmVars fv) ps}
  freeVars (TmEqs tms) = freeVars tms

instance Substitutable Case where
  substM (Case x ps tm) =
    pure (Case x) <**> substParams ps (substM tm)
  freeVars (Case x ps tm) =
    let fv = freeVars tm in fv{freeTmVars = foldr (Map.delete . fst) (freeTmVars fv) ps}

instance Substitutable Tag where
  substM tg = fmap (Map.findWithDefault tg tg . tags) get
  freeVars tg = mempty{freeTags = Map.singleton tg ()}

instance Substitutable a => Substitutable [a] where
  substM = substF
  freeVars = freeVarsF
instance Substitutable a => Substitutable (Maybe a) where
  substM = substF
  freeVars = freeVarsF

instance Substitutable v => Substitutable (Map.Map k v) where
  substM m = sequence (Map.map substM m)
  freeVars = error "freeVars called on a Subst (undefined behavior)"

instance Substitutable UsTm where
  substM (UsVar x) = fmap (f . Map.findWithDefault (Rename x) x . tmVars) get
    where f (Rename y) = UsVar y
          f (Replace _) = UsVar x
  substM (UsLam x tp tm) =
    freshen x >>= \ x' ->
    pure (UsLam x') <*> substM tp <*> bind x x' (substM tm)
  substM (UsApp tm1 tm2) =
    pure UsApp <*> substM tm1 <*> substM tm2
  substM (UsCase tm cs) =
    pure UsCase <*> substM tm <*> substM cs
  substM (UsIf tm1 tm2 tm3) =
    pure UsIf <*> substM tm1 <*> substM tm2 <*> substM tm3
  substM (UsTmBool b) =
    pure (UsTmBool b)
  substM (UsLet x xtm tm) =
    freshen x >>= \ x' ->
    pure (UsLet x') <*> substM xtm <*> bind x x' (substM tm)
  substM (UsAmb tms) =
    pure UsAmb <*> substM tms
  substM (UsFactorDouble wt tm) =
    pure UsFactorDouble <*> pure wt <*> substM tm
  substM (UsFactorNat wt tm) =
    pure UsFactorNat <*> pure wt <*> substM tm
  substM (UsFactorRatio wt tm) =
    pure UsFactorRatio <*> pure wt <*> substM tm
  substM (UsFail tp) =
    pure UsFail <*> substM tp
  substM (UsProd am tms) =
    pure (UsProd am) <*> substM tms
  substM (UsElimMultiplicative tm xs tm') =
    pure UsElimMultiplicative <*> substM tm
      <**> fmap (\ (ps, a) -> (fsts ps, a))
                (substParams [(x, NoTp) | x <- xs] (substM tm'))
  substM (UsElimAdditive tm n i x tm') =
    pure UsElimAdditive <*> substM tm <*> pure n <*> pure i
      <**> fmap (\ (p, a) -> (fst p, a))
                (substParam (x, NoTp) (substM tm'))
  substM (UsEqs tms) =
    pure UsEqs <*> substM tms

  freeVars (UsVar x) =
    mempty{freeTmVars = Map.singleton x NoTp}
  freeVars (UsLam x tp tm) =
    let fv = freeVars tm in fv{freeTmVars = Map.delete x (freeTmVars fv)}
  freeVars (UsApp tm1 tm2) =
    freeVars tm1 <> freeVars tm2
  freeVars (UsCase tm cs) =
    freeVars tm <> freeVars cs
  freeVars (UsIf tm1 tm2 tm3) =
    mconcat [freeVars tm1, freeVars tm2, freeVars tm3]
  freeVars (UsTmBool b) =
    mempty
  freeVars (UsLet x xtm tm) =
    freeVars xtm <> let fv = freeVars tm in fv{freeTmVars = Map.delete x (freeTmVars fv)}
  freeVars (UsAmb tms) =
    freeVars tms
  freeVars (UsFactorDouble wt tm) =
    freeVars tm
  freeVars (UsFactorNat wt tm) =
    freeVars tm
  freeVars (UsFactorRatio wt tm) =
    freeVars tm
  freeVars (UsFail tp) =
    mempty
  freeVars (UsProd am tms) =
    freeVars tms
  freeVars (UsElimMultiplicative tm xs tm') =
    freeVars tm <> let fv = freeVars tm' in fv{freeTmVars = foldr Map.delete (freeTmVars fv) xs}
  freeVars (UsElimAdditive tm n i x tm') =
    freeVars tm <> let fv = freeVars tm' in fv{freeTmVars = Map.delete x (freeTmVars fv)}
  freeVars (UsEqs tms) =
    freeVars tms
  
instance Substitutable CaseUs where
  substM (CaseUs x ps tm) =
    freshens ps >>= \ ps' ->
    pure (CaseUs x ps') <*> binds ps ps' (substM tm)
  freeVars (CaseUs x ps tm) = let fv = freeVars tm in fv{freeTmVars = foldr Map.delete (freeTmVars fv) ps}

instance Substitutable UsProg where
  substM (UsProgDefine x tp tm) =
    pure (UsProgDefine x) <*> substM tp <*> substM tm
  substM (UsProgExtern x tp) =
    pure (UsProgExtern x) <*> substM tp
  substM (UsProgData y ps cs) =
    freshens ps >>= \ ps' ->
    pure (UsProgData y ps') <*> binds ps ps' (substM cs)

  freeVars ps = error "freeVars on a UsProg"

instance Substitutable UsProgs where
  substM (UsProgs ps end) = pure UsProgs <*> substM ps <*> substM end
  freeVars ps = error "freeVars on a UsProgs"

instance Substitutable Ctor where
  substM (Ctor x tps) = pure (Ctor x) <*> substM tps
  freeVars (Ctor x tps) = freeVars tps

instance Substitutable Prog where
  substM (ProgDefine x ps tm tp) =
    pure (ProgDefine x) <**> substParams ps (substM tm) <*> substM tp
  substM (ProgExtern x ps tp) =
    pure (ProgExtern x) <*> substM ps <*> substM tp
  substM (ProgData y cs) =
    pure (ProgData y) <*> substM cs

  freeVars p = error "freeVars on a Prog"

instance Substitutable SProg where
  substM (SProgDefine x tgs tpms tp tm) =
    freshens tgs >>= \ tgs' ->
    binds tgs tgs'
      (let (tpmxs, tpmrs) = unzip [(x, r) | Forall x r <- tpms] in
         freshens tpmxs >>= \ tpmxs' ->
         let tpms' = [Forall x r | (x, r) <- zip tpmxs' tpmrs] in
          binds tpmxs tpmxs'
            (pure (SProgDefine x tgs' tpms') <*> substM tp <*> substM tm))
  substM (SProgExtern x tp) =
    pure (SProgExtern x) <*> substM tp
  substM (SProgData y tgs ps cs) =
    freshens tgs >>= \ tgs' ->
    binds tgs tgs'
      (freshens ps >>= \ ps' ->
       pure (SProgData y tgs' ps') <*> binds ps ps' (substM cs))

  freeVars p = error "freeVars on a Prog"

instance Substitutable Progs where
  substM progs@(Progs ps tm) =
    modify f >> pure Progs <*> substM ps <*> substM tm
    where f g = g{tmNames = Set.union (tmNames g)
                                      (Map.keysSet (C.tmNames (C.ctxtAddProgs progs)))}
  freeVars (Progs ps tm) =
    freeVars ps <> freeVars tm

instance Substitutable SProgs where
  substM (SProgs ps tm) =
    pure SProgs <*> substM ps <*> substM tm
  freeVars (SProgs ps tm) =
    freeVars ps <> freeVars tm

--- The following functions don't use Subst.
--- TODO: use Subst now?

{- substDatatype xi xf tp

   Rename all occurrences of datatype name xi to xf in type tp. -}
  
substDatatype :: TpName -> TpName -> Type -> Type
substDatatype xi xf (TpVar y) =
  TpVar y
substDatatype xi xf (TpData y tgs as) =
  TpData (if xi == y then xf else y) tgs (map (substDatatype xi xf) as)
substDatatype xi xf (TpArr tp1 tp2) =
  TpArr (substDatatype xi xf tp1) (substDatatype xi xf tp2)
substDatatype xi xf (TpProd am tps) =
  TpProd am [substDatatype xi xf tp | tp <- tps]
substDatatype xi xf NoTp = NoTp

{- freeDatatypes tp

   The set of datatypes used in tp. -}

freeDatatypes :: Type -> Set TpName
freeDatatypes (TpVar y) = Set.empty
freeDatatypes (TpData y tgs as) = Set.singleton y <> Set.unions (map freeDatatypes as)
freeDatatypes (TpArr tp1 tp2) = freeDatatypes tp1 <> freeDatatypes tp2
freeDatatypes (TpProd am tps) = Set.unions (map freeDatatypes tps)
freeDatatypes NoTp = Set.empty

{- substTags ytgs tp

   Adds tags to datatypes in type tp.

   - ytgs: Map from Vars (which are datatype names) to lists of Vars
     (which are tag names). -}

substTags :: Map TpName [Tag] -> Type -> Type
substTags ytgs (TpVar y) = TpVar y
substTags ytgs (TpData y [] as) =
  let as' = map (substTags ytgs) as in
    TpData y (fromMaybe [] (ytgs Map.!? y)) as'
substTags ytgs (TpData y tgs as) =
    if y `Map.member` ytgs then
      error ("can't add tags to a datatype that already has tags")
    else
      TpData y tgs (map (substTags ytgs) as)
        
substTags ytgs (TpArr tp1 tp2) =
  TpArr (substTags ytgs tp1) (substTags ytgs tp2)
substTags ytgs (TpProd am tps) =
  TpProd am (map (substTags ytgs) tps)
substTags ytgs NoTp = NoTp
