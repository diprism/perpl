-- Adapted from http://dev.stephendiehl.com/fun/006_hindley_milner.html

module Subst where
import Data.Char
import qualified Data.Map as Map
import Control.Monad.RWS.Lazy
import Exprs
import Util


----------------------------------------

data SplitVar = SplitVar String Int String
succSplitVar (SplitVar pre i suf) = SplitVar pre (succ i) suf
instance Show SplitVar where
  show (SplitVar pre i suf) = pre ++ show i ++ suf

-- Splits abc14'' into SplitVar "abc" 14 "\'\'"
splitVar :: Var -> SplitVar
splitVar x =
  let (pre, i, suf) = h True (reverse x)
      pre' = reverse pre
      i' = reverse i
      suf' = reverse suf
      i'' = if null i' then 0 else succ (read i' :: Int)
  in
    SplitVar pre' i'' suf'
  where
    h :: Bool -> String -> (String, String, String)
    h b "" = ("", "", "")
    h True ('\'' : cs) =
      let (pre, i, suf) = h True cs in
        (pre, i, '\'' : suf)
    h True (c : cs) = h False (c : cs)
    h False (c : cs)
      | isDigit c =
        let (pre, i, suf) = h False cs in
          (pre, c : i, suf)
      | otherwise = (c : cs, "", "")

-- Given a map and a var, try new var names until it is no longer in the map
newVar :: Var -> Map.Map Var a -> Var
newVar x xs = if Map.member x xs then h xs (splitVar x) else x
  where
    h xs x = let x' = show x in if Map.member x' xs then h xs (succSplitVar x) else x'

newVars :: [Var] -> Map.Map Var a -> [Var]
newVars xs m =
  foldr (\ x gxs g -> let x' = newVar x g in gxs (Map.insert x' () g)) (const []) xs (() <$ m)

----------------------------------------

data Scheme = Forall [Var] Type
type TypeEnv = Map.Map Var Scheme

extend :: TypeEnv -> (Var, Scheme) -> TypeEnv
extend g (x, s) = Map.insert x s g

data SubT = SubVar Var | SubTm Term | SubTp Type
type Subst = Map.Map Var SubT

type SubstM a = RWS () () Subst a

type FreeVars = Map.Map Var Type

compose :: Subst -> Subst -> Subst
s1 `compose` s2 = Map.map (subst s1) s2 `Map.union` s1

freshen :: Var -> SubstM Var
freshen x =
  get >>= \ s ->
  let x' = newVar x s in
  -- add x->x and x'->x' to state
  put (Map.insert x (SubVar x) (Map.insert x' (SubVar x') s)) >>
  return x'

freshens :: [Var] -> SubstM [Var]
freshens = sequence . fmap freshen

bind :: Var -> Var -> SubstM a -> SubstM a
bind x x' m =
  get >>= \ s ->
  put (Map.insert x (SubVar x') (Map.insert x' (SubVar x') s)) >>
  m >>= \ a ->
  get >>= \ s' ->
  put (Map.insert x (SubVar x) (Map.insert x' (SubVar x') s')) >>
  return a

binds :: [Var] -> [Var] -> SubstM a -> SubstM a
binds xs xs' m = foldr (uncurry bind) m (zip xs xs')

substVT :: Var -> SubstM SubT
substVT x = get >>= \ s -> return (maybe (SubVar x) id (Map.lookup x s))

substVar :: Var -> (Var -> a) -> (Term -> a) -> (Type -> a) -> a -> SubstM a
substVar x fv ftm ftp fn =
  get >>= \ s ->
  return $ maybe fn
    (\ st -> case st of
        {SubVar x' -> fv x'; SubTm tm -> ftm tm; SubTp tp -> ftp tp })
    (Map.lookup x s)

substParams :: [Param] -> SubstM a -> SubstM ([Param], a)
substParams [] cont = (,) [] <$> cont
substParams ((x, tp) : ps) cont =
  freshen x >>= \ x' ->
  substM tp >>= \ tp' ->
  bind x x' (substParams ps cont) >>= \ (ps', a) ->
  return ((x', tp') : ps', a)

class Substitutable a where
  freeVars :: a -> FreeVars
  substM :: a -> SubstM a
  
  subst :: Subst -> a -> a
  subst r a = let (a', r', ()) = runRWS (substM a) () r in a'

  alphaRename :: a -> a
  alphaRename = subst Map.empty

substF :: (Functor t, Traversable t, Substitutable a) => t a -> SubstM (t a)
substF fa = sequence (fmap substM fa)

freeVarsF :: (Foldable f, Substitutable a) => f a -> FreeVars
freeVarsF = foldr (\ a -> Map.union (freeVars a)) Map.empty

instance Substitutable Scheme where
  substM (Forall xs tp) =
    freshens xs >>= \ xs' ->
    pure (Forall xs') <*> binds xs xs' (substM tp)

  freeVars (Forall xs tp) = foldr Map.delete (freeVars tp) xs
    
instance Substitutable Type where
  substM (TpArr tp1 tp2) = pure TpArr <*> substM tp1 <*> substM tp2
  substM (TpVar y) =
    substVar y TpVar (const (TpVar y)) id (TpVar y)
  substM (TpProd am tps) = pure (TpProd am) <*> substM tps
  substM NoTp = pure NoTp

  freeVars (TpArr tp1 tp2) = Map.union (freeVars tp1) (freeVars tp2)
  freeVars (TpVar y) = Map.empty -- Map.singleton y ()
  freeVars (TpProd am tps) = Map.unions [freeVars tp | tp <- tps]
  freeVars NoTp = Map.empty

instance Substitutable Term where
  substM (TmVarL x tp) =
    let tmx x' = pure (TmVarL x') <*> substM tp in
      substVar x tmx pure (const (tmx x)) (tmx x) >>= id
  substM (TmVarG g x as tp) =
    pure (TmVarG g x) <*> substM as <*> substM tp
  substM (TmLam x xtp tm tp) =
    freshen x >>= \ x' ->
    pure (TmLam x') <*> substM xtp <*> bind x x' (substM tm) <*> substM tp
  substM (TmApp tm1 tm2 tp2 tp) =
    pure TmApp <*> substM tm1 <*> substM tm2 <*> pure tp2 <*> pure tp
  substM (TmLet x xtm xtp tm tp) =
    freshen x >>= \ x' ->
    pure (TmLet x') <*> substM xtm <*> substM xtp <*> bind x x' (substM tm) <*> substM tp
  substM (TmCase tm y cs tp) =
    pure TmCase <*> substM tm <*> pure y <*> substM cs <*> substM tp
  substM (TmSamp d tp) =
    pure (TmSamp d) <*> substM tp
  substM (TmAmb tms tp) =
    pure TmAmb <*> substM tms <*> pure tp
  substM (TmProd am as) =
    pure (TmProd am) <*> substM as
  substM (TmElimAmp tm tps i) =
    pure TmElimAmp <*> substM tm <*> substM tps <*> pure i
  substM (TmElimProd ptm ps tm tp) =
    pure TmElimProd <*> substM ptm <**> substParams ps (substM tm) <*> substM tp
  substM (TmEqs tms) =
    pure TmEqs <*> substM tms
  
  freeVars (TmVarL x tp) = Map.singleton x tp
  freeVars (TmVarG g x as tp) = freeVars as
  freeVars (TmLam x xtp tm tp) = Map.delete x (freeVars tm)
  freeVars (TmApp tm1 tm2 tp2 tp) = Map.union (freeVars tm1) (freeVars tm2)
  freeVars (TmLet x xtm xtp tm tp) = Map.union (freeVars xtm) (Map.delete x (freeVars tm))
  freeVars (TmCase tm y cs tp) = Map.union (freeVars tm) (freeVars cs)
  freeVars (TmSamp d tp) = Map.empty
  freeVars (TmAmb tms tp) = freeVars tms
  freeVars (TmProd am as) = freeVars as
  freeVars (TmElimAmp tm tps i) = freeVars tm
  freeVars (TmElimProd ptm ps tm tp) = Map.union (freeVars ptm) (foldr (Map.delete . fst) (freeVars tm) ps)
  freeVars (TmEqs tms) = freeVars tms

instance Substitutable Case where
  substM (Case x ps tm) =
    pure (Case x) <**> substParams ps (substM tm)
  freeVars (Case x ps tm) =
    foldr (Map.delete . fst) (freeVars tm) ps

instance Substitutable a => Substitutable [a] where
  substM = substF
  freeVars = freeVarsF
instance Substitutable a => Substitutable (Maybe a) where
  substM = substF
  freeVars = freeVarsF

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
  substM (a, b) = pure (,) <*> substM a <*> substM b
  freeVars (a, b) = Map.union (freeVars a) (freeVars b)

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
  substM (UsSamp d tp) =
    pure (UsSamp d) <*> substM tp
  substM (UsLet x xtm tm) =
    freshen x >>= \ x' ->
    pure (UsLet x') <*> substM xtm <*> bind x x' (substM tm)
  substM (UsAmb tms) =
    pure UsAmb <*> substM tms
  substM (UsElimAmp tm o) =
    pure UsElimAmp <*> substM tm <*> pure o
  substM (UsProd am tms) =
    pure (UsProd am) <*> substM tms
  substM (UsElimProd tm xs tm') =
    freshens xs >>= \ xs' ->
    pure UsElimProd <*> substM tm <*> pure xs' <*> binds xs xs' (substM tm')
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
  freeVars (UsSamp d tp) =
    Map.empty
  freeVars (UsLet x xtm tm) =
    Map.union (freeVars xtm) (Map.delete x (freeVars tm))
  freeVars (UsAmb tms) =
    freeVars tms
  freeVars (UsElimAmp tm o) =
    freeVars tm
  freeVars (UsProd am tms) =
    freeVars tms
  freeVars (UsElimProd tm xs tm') =
    Map.union (freeVars tm) (foldr Map.delete (freeVars tm') xs)
  freeVars (UsEqs tms) =
    freeVars tms
  
instance Substitutable CaseUs where
  substM (CaseUs x ps tm) =
    freshens ps >>= \ ps' ->
    pure (CaseUs x ps') <*> binds ps ps' (substM tm)
  freeVars (CaseUs x ps tm) = foldr Map.delete (freeVars tm) ps

instance Substitutable UsProgs where
  substM (UsProgExec tm) =
    pure UsProgExec <*> substM tm
  substM (UsProgFun x tp tm ps) =
    bind x x okay >>
    pure (UsProgFun x) <*> substM tp <*> substM tm <*> substM ps
  substM (UsProgExtern x tp ps) =
    bind x x okay >>
    pure (UsProgExtern x) <*> substM tp <*> substM ps
  substM (UsProgData y cs ps) =
    bind y y okay >>
    pure (UsProgData y) <*> substM cs <*> substM ps

  freeVars (UsProgExec tm) =
    freeVars tm
  freeVars (UsProgFun x tp tm ps) =
    Map.unions [freeVars tm, freeVars tp, freeVars ps]
  freeVars (UsProgExtern x tp ps) =
    Map.union (freeVars tp) (freeVars ps)
  freeVars (UsProgData y cs ps) =
    Map.union (freeVars cs) (freeVars ps)

instance Substitutable Ctor where
  substM (Ctor x tps) = pure (Ctor x) <*> substM tps
  freeVars (Ctor x tps) = freeVars tps

instance Substitutable Prog where
  substM (ProgFun x ps tm tp) =
    bind x x okay >>
    pure (ProgFun x) <**> substParams ps (substM tm) <*> substM tp
  substM (ProgExtern x xp ps tp) =
    bind x x okay >>
    bind xp xp okay >>
    pure (ProgExtern x xp) <*> substM ps <*> substM tp
  substM (ProgData y cs) =
    bind y y okay >>
    pure (ProgData y) <*> substM cs

  freeVars (ProgFun x ps tm tp) =
    let (pxs, ptps) = unzip ps in
      foldr Map.delete (Map.unions [freeVars tm, freeVars tp, freeVars ptps]) pxs
  freeVars (ProgExtern x xp ps tp) =
    freeVars (ps ++ [tp])
  freeVars (ProgData y cs) =
    freeVars cs

instance Substitutable Progs where
  substM (Progs ps tm) =
    pure Progs <*> substM ps <*> substM tm
  freeVars (Progs ps tm) =
    Map.union (freeVars ps) (freeVars tm)
