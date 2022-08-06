-- Adapted from http://dev.stephendiehl.com/fun/006_hindley_milner.html
{- Substitution code -}

module Scope.Subst (SubT(..), Subst, compose,
                    Substitutable,
                    substM, runSubst, subst, substWithCtxt, alphaRename,
                    FreeVars, freeVars,
                    freshens, freshVar) where
import qualified Data.Map as Map
import Control.Monad.RWS.Lazy
import Util.Helpers
import Scope.Ctxt (Ctxt)
import Scope.Fresh (newVar)
import Struct.Lib

----------------------------------------

data SubT = SubVar Var | SubTm Term | SubTp Type
  deriving (Eq, Ord, Show)
type Subst = Map Var SubT

-- Composes two substitutions
compose :: Subst -> Subst -> Subst
s1 `compose` s2 = Map.map (subst s1) s2 `Map.union` s1

-- State monad, where s = Subst
type SubstM = RWS () () Subst

-- Returns a map of vars and their types (if a term var)
-- If a var is a type var, the type will be NoType
type FreeVars = Map Var Type

-- Runs the substitution monad
runSubst :: Subst -> SubstM a -> a
runSubst s r = let (a', r', ()) = runRWS r () s in a'

-- Picks a fresh name derived from x
freshen :: Var -> SubstM Var
freshen "_" = freshen "_0" -- get rid of '_'s
freshen x =
  fmap (newVar x) get >>= \ x' ->
  modify (Map.insert x' (SubVar x')) >>
  return x'

-- Pick fresh names for a list of vars
freshens :: [Var] -> SubstM [Var]
freshens [] = return []
freshens (x : xs) = freshen x >>= \ x' -> pure ((:) x') <*> bind x x' (freshens xs)

-- Rename x to x' in m
bind :: Var -> Var -> SubstM a -> SubstM a
bind x x' m =
  substVT x >>= \ oldx ->
  substVT x' >>= \ oldx' ->
  modify (Map.insert x (SubVar x')) >>
  modify (Map.insert x' (SubVar x')) >>
  m >>= \ a ->
  modify (Map.insert x oldx) >>
  modify (Map.insert x' oldx') >>
  return a

-- Renames all xs to xs' in m
binds :: [Var] -> [Var] -> SubstM a -> SubstM a
binds xs xs' m = foldr (uncurry bind) m (zip xs xs')

-- Lookup a variable
substVT :: Var -> SubstM SubT
substVT x = get >>= \ s -> return (maybe (SubVar x) id (Map.lookup x s))

-- Lookup a variable, with continuations for var, term, type, and if undefined
substVar :: Var -> (Var -> a) -> (Term -> a) -> (Type -> a) -> a -> SubstM a
substVar x fv ftm ftp fn =
  get >>= \ s ->
  return $ maybe fn
    (\ st -> case st of
        {SubVar x' -> fv x'; SubTm tm -> ftm tm; SubTp tp -> ftp tp })
    (Map.lookup x s)

-- Freshens params, and binds them in cont
substParams :: AddMult -> [Param] -> SubstM a -> SubstM ([Param], a)
substParams am [] cont = (,) [] <$> cont
substParams Additive (("_", tp) : ps) cont =
  substM tp >>= \ tp' ->
  substParams Additive ps cont >>= \ (ps', a) ->
  return (("_", tp') : ps', a)
substParams am ((x, tp) : ps) cont =
  freshen x >>= \ x' ->
  substM tp >>= \ tp' ->
  bind x x' (substParams am ps cont) >>= \ (ps', a) ->
  return ((x', tp') : ps', a)

-- "Substitutable" typeclass definition: must have freeVars and substM
class Substitutable a where
  freeVars :: a -> FreeVars
  substM :: a -> SubstM a

-- Run substM
subst :: Substitutable a => Subst -> a -> a
subst r a = runSubst r (substM a)

-- Run substM under a given context
substWithCtxt :: Substitutable a => Ctxt -> Subst -> a -> a
substWithCtxt g s = subst (Map.union (Map.mapWithKey (const . SubVar) g) s)

-- Run substM with no substitutions, so just alpha-rename bound vars
alphaRename :: Substitutable a => Ctxt -> a -> a
alphaRename g = substWithCtxt g Map.empty

-- Substitutes inside a Functor/Traversable t
substF :: (Functor t, Traversable t, Substitutable a) => t a -> SubstM (t a)
substF = mapM substM

-- Returns all free vars in a foldable
freeVarsF :: (Foldable f, Substitutable a) => f a -> FreeVars
freeVarsF = foldMap freeVars


instance Substitutable Type where
  substM (TpArr tp1 tp2) = pure TpArr <*> substM tp1 <*> substM tp2
  substM tp@(TpVar y) =
    substVar y TpVar (const tp) id tp
  substM (TpData y tgs as) =
    substM tgs >>= \ tgs' ->
    substM as >>= \ as' ->
    substVar y
      (\ y' -> TpData y' tgs' as')
      (const (TpData y tgs' as'))
      -- Allow y := y' tg1 ....
      -- This is used in TypeInf.Solve in inferData to add tags to a datatype.
      (\ tp' -> case tp' of TpData y' tgs'' [] -> TpData y' (tgs'' ++ tgs') as'
                            _ -> error ("kind error (" ++ y ++ " := " ++ show tp' ++ ")"))
      (TpData y tgs' as')
  substM (TpProd am tps) = pure (TpProd am) <*> substM tps
  substM NoTp = pure NoTp

  freeVars (TpArr tp1 tp2) = Map.union (freeVars tp1) (freeVars tp2)
  freeVars (TpVar y) = Map.singleton y NoTp
  freeVars (TpData y tgs as) = Map.singleton y NoTp <> freeVars tgs <> freeVars as
  freeVars (TpProd am tps) = Map.unions (freeVars <$> tps)
  freeVars NoTp = Map.empty

instance Substitutable Term where
  substM (TmVarL x tp) =
    let tmx x' = pure (TmVarL x') <*> substM tp in
      substVar x tmx pure (const (tmx x)) (tmx x) >>= id
  substM (TmVarG g x tgs tis as tp) =
    pure (TmVarG g x) <*> substM tgs <*> substM tis <*> mapArgsM substM as <*> substM tp -- TODO: for consistency, should x be substitutable?
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
  substM (TmFactor wt tm tp) =
    pure TmFactor <*> pure wt <*> substM tm <*> substM tp
  substM (TmProd am as) =
    pure (TmProd am) <*> mapArgsM substM as
--  substM (TmElimAmp tm i tp) =
--    pure TmElimAmp <*> substM tm <*> pure i <*> substM tp
  substM (TmElimProd am ptm ps tm tp) =
    pure (TmElimProd am) <*> substM ptm <**> substParams am ps (substM tm) <*> substM tp
  substM (TmEqs tms) =
    pure TmEqs <*> substM tms
  
  freeVars (TmVarL x tp) = Map.singleton x tp
  freeVars (TmVarG g x tgs tis as tp) = freeVars tgs <> freeVars tis <> freeVars (fsts as) -- TODO: for consistency, should x be included?
  freeVars (TmLam x xtp tm tp) = Map.delete x (freeVars tm)
  freeVars (TmApp tm1 tm2 tp2 tp) = Map.union (freeVars tm1) (freeVars tm2)
  freeVars (TmLet x xtm xtp tm tp) = Map.union (freeVars xtm) (Map.delete x (freeVars tm))
  freeVars (TmCase tm y cs tp) = Map.union (freeVars tm) (freeVars cs)
  freeVars (TmAmb tms tp) = freeVars tms
  freeVars (TmFactor wt tm tp) = freeVars tm
  freeVars (TmProd am as) = freeVars (fsts as)
--  freeVars (TmElimAmp tm i tp) = freeVars tm
  freeVars (TmElimProd am ptm ps tm tp) = Map.union (freeVars ptm) (foldr (Map.delete . fst) (freeVars tm) ps)
  freeVars (TmEqs tms) = freeVars tms

instance Substitutable Case where
  substM (Case x ps tm) =
    pure (Case x) <**> substParams Multiplicative ps (substM tm)
  freeVars (Case x ps tm) =
    foldr (Map.delete . fst) (freeVars tm) ps

instance Substitutable a => Substitutable [a] where
  substM = substF
  freeVars = freeVarsF
instance Substitutable a => Substitutable (Maybe a) where
  substM = substF
  freeVars = freeVarsF

instance Substitutable SubT where
  substM (SubTm tm) = pure SubTm <*> substM tm
  substM (SubTp tp) = pure SubTp <*> substM tp
  substM (SubVar x) = substVT x

  freeVars (SubTm tm) = freeVars tm
  freeVars (SubTp tp) = freeVars tp
  freeVars (SubVar x) = Map.singleton x NoTp

instance Substitutable v => Substitutable (Map.Map k v) where
  substM m = sequence (Map.map substM m)
  freeVars = error "freeVars called on a Subst (undefined behavior)"

instance Substitutable UsTm where
  substM (UsVar x) =
    pure UsVar <*> substVar x id (const x) (const x) x
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
  substM (UsFactor wt tm) =
    pure UsFactor <*> pure wt <*> substM tm
  substM (UsFail tp) =
    pure UsFail <*> substM tp
  substM (UsProd am tms) =
    pure (UsProd am) <*> substM tms
  substM (UsElimProd am tm xs tm') =
    pure (UsElimProd am) <*> substM tm
      <**> fmap (\ (ps, a) -> (fsts ps, a))
                (substParams am [(x, NoTp) | x <- xs] (substM tm'))
  substM (UsEqs tms) =
    pure UsEqs <*> substM tms

  freeVars (UsVar x) =
    Map.singleton x NoTp
  freeVars (UsLam x tp tm) =
    Map.delete x (freeVars tm)
  freeVars (UsApp tm1 tm2) =
    Map.union (freeVars tm1) (freeVars tm2)
  freeVars (UsCase tm cs) =
    Map.union (freeVars tm) (freeVars cs)
  freeVars (UsIf tm1 tm2 tm3) =
    Map.unions [freeVars tm1, freeVars tm2, freeVars tm3]
  freeVars (UsTmBool b) =
    Map.empty
  freeVars (UsLet x xtm tm) =
    Map.union (freeVars xtm) (Map.delete x (freeVars tm))
  freeVars (UsAmb tms) =
    freeVars tms
  freeVars (UsFactor wt tm) =
    freeVars tm
  freeVars (UsFail tp) =
    Map.empty
--  freeVars (UsElimAmp tm o) =
--    freeVars tm
  freeVars (UsProd am tms) =
    freeVars tms
  freeVars (UsElimProd am tm xs tm') =
    Map.union (freeVars tm) (foldr Map.delete (freeVars tm') xs)
  freeVars (UsEqs tms) =
    freeVars tms
  
instance Substitutable CaseUs where
  substM (CaseUs x ps tm) =
    freshens ps >>= \ ps' ->
    pure (CaseUs x ps') <*> binds ps ps' (substM tm)
  freeVars (CaseUs x ps tm) = foldr Map.delete (freeVars tm) ps

instance Substitutable UsProg where
  substM (UsProgFun x tp tm) =
    bind x x okay >>
    pure (UsProgFun x) <*> substM tp <*> substM tm
  substM (UsProgExtern x tp) =
    bind x x okay >>
    pure (UsProgExtern x) <*> substM tp
  substM (UsProgData y ps cs) =
    bind y y okay >>
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
  substM (ProgFun x ps tm tp) =
    bind x x okay >>
    pure (ProgFun x) <**> substParams Multiplicative ps (substM tm) <*> substM tp
  substM (ProgExtern x ps tp) =
    bind x x okay >>
    pure (ProgExtern x) <*> substM ps <*> substM tp
  substM (ProgData y cs) =
    bind y y okay >>
    pure (ProgData y) <*> substM cs

  freeVars p = error "freeVars on a Prog"

instance Substitutable SProg where
  substM (SProgFun x tgs tpms tp tm) =
    bind x x okay >>
    freshens tgs >>= \ tgs' ->
    binds tgs tgs'
      (freshens tpms >>= \ tpms' ->
       binds tpms tpms'
         (pure (SProgFun x tgs' tpms') <*> substM tp <*> substM tm))
  substM (SProgExtern x tp) =
    bind x x okay >>
    pure (SProgExtern x) <*> substM tp
  substM (SProgData y tgs ps cs) =
    bind y y okay >>
    freshens tgs >>= \ tgs' ->
    binds tgs tgs'
      (freshens ps >>= \ ps' ->
       pure (SProgData y tgs' ps') <*> binds ps ps' (substM cs))

  freeVars p = error "freeVars on a Prog"

instance Substitutable Progs where
  substM (Progs ps tm) =
    pure Progs <*> substM ps <*> substM tm
  freeVars (Progs ps tm) =
    Map.union (freeVars ps) (freeVars tm)

instance Substitutable SProgs where
  substM (SProgs ps tm) =
    pure SProgs <*> substM ps <*> substM tm
  freeVars (SProgs ps tm) =
    Map.union (freeVars ps) (freeVars tm)


freshVar' :: Subst -> Var -> Var
freshVar' s x =
  let (x', r', ()) = runRWS (freshen x) () s in x'

freshVar :: Ctxt -> Var -> Var
freshVar = freshVar' . Map.mapWithKey (const . SubVar)
