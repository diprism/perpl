-- Adapted from http://dev.stephendiehl.com/fun/006_hindley_milner.html
{- Substitution code -}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, StandaloneDeriving #-}

module Scope.Subst where
import qualified Data.Map as Map
import Control.Applicative (Alternative((<|>)))
import Data.Foldable (toList)
import Control.Monad.RWS.Lazy
import Util.Helpers
import Util.None
import Scope.Ctxt
import Scope.Fresh
import Struct.Lib

----------------------------------------

data SubT dparams = SubVar Var | SubTm (Term dparams) | SubTp (Type dparams)
deriving instance Eq (SubT [])
deriving instance Eq (SubT None)
deriving instance Ord (SubT [])
deriving instance Ord (SubT None)
deriving instance Show (SubT [])
deriving instance Show (SubT None)
type Subst dparams = Map Var (SubT dparams)

-- Composes two substitutions
compose :: (Traversable dparams, Alternative dparams) => Subst dparams -> Subst dparams -> Subst dparams
s1 `compose` s2 = Map.map (subst s1) s2 `Map.union` s1

-- State monad, where s = Subst
type SubstM dparams = RWS () () (Subst dparams)

-- Returns a map of vars and their types (if a term var)
-- If a var is a type var, the type will be NoType
type FreeVars dparams = Map Var (Type dparams)

-- Runs the substitution monad
runSubst :: Subst dparams -> SubstM dparams a -> a
runSubst s r = let (a', r', ()) = runRWS r () s in a'

-- Picks a fresh name derived from x
freshen :: Var -> SubstM dparams Var
freshen "_" = freshen "_0" -- get rid of '_'s
freshen x =
  fmap (newVar x) get >>= \ x' ->
  modify (Map.insert x' (SubVar x')) >>
  return x'

-- Pick fresh names for a list of vars
{-
freshens :: [Var] -> SubstM [Var]
freshens [] = return []
freshens (x : xs) = freshen x >>= \ x' -> pure ((:) x') <*> bind x x' (freshens xs)
-}
freshens :: Traversable t => t Var -> SubstM dparams (t Var)
freshens xs = traverse freshen' xs >>= traverse cleanup where
  freshen' :: Var -> SubstM dparams (Var, Var, SubT dparams, SubT dparams)
  freshen' x = freshen x >>= \ x' ->
               substVT x >>= \ oldx ->
               substVT x' >>= \ oldx' ->
               modify (Map.insert x (SubVar x')) >>
               modify (Map.insert x' (SubVar x')) >>
               return (x, x', oldx, oldx')
  cleanup :: (Var, Var, SubT dparams, SubT dparams) -> SubstM dparams Var
  cleanup (x, x', oldx, oldx') =
               modify (Map.insert x oldx) >>
               modify (Map.insert x' oldx') >>
               return x'

-- Rename x to x' in m
bind :: Var -> Var -> SubstM dparams a -> SubstM dparams a
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
binds :: (Foldable t, Applicative t) => t Var -> t Var -> SubstM dparams a -> SubstM dparams a
binds xs xs' m = foldr (uncurry bind) m (zip (toList xs) (toList xs'))

-- Lookup a variable
substVT :: Var -> SubstM dparams (SubT dparams)
substVT x = get >>= \ s -> return (maybe (SubVar x) id (Map.lookup x s))

-- Lookup a variable, with continuations for var, term, type, and if undefined
substVar :: Var -> (Var -> a) -> (Term dparams -> a) -> (Type dparams -> a) -> a -> SubstM dparams a
substVar x fv ftm ftp fn =
  get >>= \ s ->
  return $ maybe fn
    (\ st -> case st of
        {SubVar x' -> fv x'; SubTm tm -> ftm tm; SubTp tp -> ftp tp })
    (Map.lookup x s)

-- Freshens params, and binds them in cont
substParams :: (Traversable dparams, Alternative dparams) => AddMult -> [Param dparams] -> SubstM dparams a -> SubstM dparams ([Param dparams], a)
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
class Substitutable a dparams where
  freeVars :: a -> FreeVars dparams
  substM :: a -> SubstM dparams a

-- Run substM
subst :: Substitutable a dparams => Subst dparams -> a -> a
subst r a = runSubst r (substM a)

-- Run substM under a given context
substWithCtxt :: Substitutable a dparams => Ctxt tags tparams dparams -> Subst dparams -> a -> a
substWithCtxt g s = subst (Map.union (Map.mapWithKey (const . SubVar) g) s)

-- Run substM with no substitutions, so just alpha-rename bound vars
alphaRename :: Substitutable a dparams => Ctxt tags tparams dparams -> a -> a
alphaRename g = substWithCtxt g Map.empty

-- Substitutes inside a Functor/Traversable t
substF :: (Functor t, Traversable t, Substitutable a dparams) => t a -> SubstM dparams (t a)
substF = mapM substM

-- Returns all free vars in a foldable
freeVarsF :: (Foldable f, Substitutable a dparams) => f a -> FreeVars dparams
freeVarsF = foldMap freeVars


instance (Traversable dparams, Alternative dparams) => Substitutable (Type dparams) dparams where
  substM (TpArr tp1 tp2) = pure TpArr <*> substM tp1 <*> substM tp2
  substM tp@(TpVar y) =
    substVar y TpVar (const tp) id tp
  substM tp@(TpData y as) =
    substF as >>= \ as' ->
    substVar y
      (\ y' -> TpData y' as')
      (const (TpData y as'))
      (\ tp' -> case tp' of TpData y' bs -> TpData y' (bs <|> as')
                            _ -> error ("kind error (" ++ show tp ++ " := " ++ show tp' ++ ")"))
      (TpData y as')
  substM (TpProd am tps) = pure (TpProd am) <*> substM tps
  substM NoTp = pure NoTp

  freeVars (TpArr tp1 tp2) = Map.union (freeVars tp1) (freeVars tp2)
  freeVars (TpVar y) = Map.singleton y NoTp
  freeVars (TpData y as) = Map.singleton y NoTp <> freeVarsF as
  freeVars (TpProd am tps) = Map.unions (freeVars <$> tps)
  freeVars NoTp = Map.empty

instance (Traversable dparams, Alternative dparams) => Substitutable (Term dparams) dparams where
  substM (TmVarL x tp) =
    let tmx = \x' -> TmVarL x' <$> substM tp in
      substVar x tmx pure (const (tmx x)) (tmx x) >>= id
  substM (TmVarG g x tis as tp) =
    pure (TmVarG g x) <*> substM tis <*> mapArgsM substM as <*> substM tp
  substM (TmLam x xtp tm tp) =
    freshen x >>= \ x' ->
    pure (TmLam x') <*> substM xtp <*> bind x x' (substM tm) <*> substM tp
  substM (TmApp tm1 tm2 tp2 tp) =
    pure TmApp <*> substM tm1 <*> substM tm2 <*> substM tp2 <*> substM tp
  substM (TmLet x xtm xtp tm tp) =
    freshen x >>= \ x' ->
    pure (TmLet x') <*> substM xtm <*> substM xtp <*> bind x x' (substM tm) <*> substM tp
  substM (TmCase tm (y, as) cs tp) =
    pure TmCase <*> substM tm <*> (pure ((,) y) <*> substM as) <*> substM cs <*> substM tp
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
  freeVars (TmVarG g x tis as tp) = freeVars (fsts as)
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

instance (Traversable dparams, Alternative dparams) => Substitutable (Case dparams) dparams where
  substM (Case x ps tm) =
    pure (Case x) <**> substParams Multiplicative ps (substM tm)
  freeVars (Case x ps tm) =
    foldr (Map.delete . fst) (freeVars tm) ps

instance (Substitutable a dparams) => Substitutable [a] dparams where
  substM = substF
  freeVars = freeVarsF
instance (Substitutable a dparams) => Substitutable (Maybe a) dparams where
  substM = substF
  freeVars = freeVarsF
instance (Substitutable a dparams) => Substitutable (Map k a) dparams where
  substM = substF
  freeVars = freeVarsF

instance (Traversable dparams, Alternative dparams) => Substitutable (SubT dparams) dparams where
  substM (SubTm tm) = pure SubTm <*> substM tm
  substM (SubTp tp) = pure SubTp <*> substM tp
  substM (SubVar x) = substVT x

  freeVars (SubTm tm) = freeVars tm
  freeVars (SubTp tp) = freeVars tp
  freeVars (SubVar x) = Map.singleton x NoTp

instance (Traversable dparams, Alternative dparams) => Substitutable (UsTm dparams) dparams where
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
  
instance (Traversable dparams, Alternative dparams) => Substitutable (CaseUs dparams) dparams where
  substM (CaseUs x ps tm) =
    freshens ps >>= \ ps' ->
    pure (CaseUs x ps') <*> binds ps ps' (substM tm)
  freeVars (CaseUs x ps tm) = foldr Map.delete (freeVars tm) ps

instance Substitutable UsProg [] where
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

instance Substitutable UsProgs [] where
  substM (UsProgs ps end) = pure UsProgs <*> substM ps <*> substM end
  freeVars ps = error "freeVars on a UsProgs"

instance (Traversable dparams, Alternative dparams) => Substitutable (Ctor dparams) dparams where
  substM (Ctor x tps) = Ctor x <$> substM tps
  freeVars (Ctor x tps) = freeVars tps

instance Substitutable Prog None where
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

instance Substitutable SProg [] where
  substM (SProgFun x (Forall tgs tpms tp) tm) =
    bind x x okay >>
    freshens tgs >>= \ tgs' ->
    binds tgs tgs'
      (freshens tpms >>= \ tpms' ->
       binds tpms tpms'
         (pure (SProgFun x) <*> (pure (Forall tgs' tpms') <*> substM tp) <*> substM tm))
  substM (SProgExtern x tps tp) =
    bind x x okay >>
    pure (SProgExtern x) <*> substM tps <*> substM tp
  substM (SProgData y tgs ps cs) =
    bind y y okay >>
    freshens tgs >>= \ tgs' ->
    binds tgs tgs'
      (freshens ps >>= \ ps' ->
       pure (SProgData y tgs' ps') <*> binds ps ps' (substM cs))

  freeVars p = error "freeVars on a Prog"

instance Substitutable Progs None where
  substM (Progs ps tm) =
    pure Progs <*> substM ps <*> substM tm
  freeVars (Progs ps tm) =
    Map.union (freeVars ps) (freeVars tm)

instance Substitutable SProgs [] where
  substM (SProgs ps tm) =
    pure SProgs <*> substM ps <*> substM tm
  freeVars (SProgs ps tm) =
    Map.union (freeVars ps) (freeVars tm)


freshVar' :: Subst dparams -> Var -> Var
freshVar' s x =
  let (x', r', ()) = runRWS (freshen x) () s in x'

freshVar :: Ctxt tags tparams dparams -> Var -> Var
freshVar = freshVar' . Map.mapWithKey (const . SubVar)


instance (Traversable tparams, Applicative tparams) => Substitutable (CtxtDef None tparams None) None where
  substM (DefLocalTerm tp) = DefLocalTerm <$> substM tp
  substM (DefGlobalTerm tgs xs tp) =
    freshens tgs >>= \ tgs' ->
    binds tgs tgs'
      (freshens xs >>= \ xs' ->
       DefGlobalTerm tgs xs' <$> binds xs xs' (substM tp))
  substM (DefCtorTerm tgs xs tp) =
    freshens tgs >>= \ tgs' ->
    binds tgs tgs'
      (freshens xs >>= \ xs' ->
       DefCtorTerm tgs xs' <$> binds xs xs' (substM tp))
  substM (DefData None None cs) = DefData None None <$> substM cs
  
  freeVars (DefLocalTerm         tp) = freeVars tp
  freeVars (DefGlobalTerm tgs xs tp) = foldr Map.delete (foldr Map.delete (freeVars tp) xs) tgs
  freeVars (DefCtorTerm   tgs xs tp) = foldr Map.delete (foldr Map.delete (freeVars tp) xs) tgs
  freeVars (DefData None None cs)    = freeVars cs

instance Substitutable Scheme [] where
  substM (Forall tgs xs tp) =
    freshens tgs >>= \ tgs' ->
    binds tgs tgs'
      (freshens xs >>= \ xs' ->
       Forall tgs xs' <$> binds xs xs' (substM tp))

  freeVars (Forall tgs xs tp) = foldr Map.delete (foldr Map.delete (freeVars tp) xs) tgs
