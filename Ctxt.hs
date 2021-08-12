module Ctxt where
import qualified Data.Map as Map
import Exprs
import Util

data Scope = ScopeLocal | ScopeGlobal | ScopeCtor
  deriving Eq

data CtxtDef =
    DefTerm Scope Type
  | DefData [Ctor]

type Ctxt = Map.Map Var CtxtDef

-- Default context
emptyCtxt :: Ctxt
emptyCtxt = Map.empty

-- Add a local term to the context
ctxtDeclTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDeclTerm g x tp = Map.insert x (DefTerm ScopeLocal tp) g

ctxtDeclArgs :: Ctxt -> [Param] -> Ctxt
ctxtDeclArgs = foldl $ uncurry . ctxtDeclTerm

-- Add a global term to the context
ctxtDefTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDefTerm g x tp = Map.insert x (DefTerm ScopeGlobal tp) g

-- Add a constructor to the context
ctxtDefCtor :: Ctxt -> Ctor -> Var -> Ctxt
ctxtDefCtor g (Ctor x tps) y =
  Map.insert x (DefTerm ScopeCtor (foldr TpArr (TpVar y) tps)) g

-- Add a datatype definition to the context,
-- and all its constructors
ctxtDeclType :: Ctxt -> Var -> [Ctor] -> Ctxt
ctxtDeclType g y ctors =
  foldr (\ c g -> ctxtDefCtor g c y)
    (Map.insert y (DefData ctors) g) ctors

-- Lookup a term in the context
ctxtLookupTerm :: Ctxt -> Var -> Maybe (Scope, Type)
ctxtLookupTerm g x = Map.lookup x g >>= \ vd -> case vd of
  DefTerm sc tp -> Just (sc, tp)
  DefData cs -> Nothing

-- Lookup a datatype in the context
ctxtLookupType :: Ctxt -> Var -> Maybe [Ctor]
ctxtLookupType g x = Map.lookup x g >>= \ vd -> case vd of
  DefData cs -> Just cs
  _ -> Nothing

-- Is this var bound in this context?
ctxtBinds :: Ctxt -> Var -> Bool
ctxtBinds = flip Map.member

-- Adds all definitions from a file to context
ctxtDefProg :: Ctxt -> Prog -> Ctxt
ctxtDefProg g (ProgFun x ps tm tp) = ctxtDefTerm g x (joinArrows (map snd ps) tp)
ctxtDefProg g (ProgExtern x xp ps tp) = ctxtDefTerm g x (joinArrows ps tp)
ctxtDefProg g (ProgData y cs) = ctxtDeclType g y cs

-- Populates a context with the definitions from a file
ctxtDefProgs :: Progs -> Ctxt
ctxtDefProgs (Progs ps end) = foldl ctxtDefProg emptyCtxt ps

-- Adds all definitions from a raw file to context
ctxtDefUsProgs' :: Ctxt -> UsProgs -> Ctxt
ctxtDefUsProgs' g (UsProgFun x tp tm ps) = ctxtDefUsProgs' (ctxtDefTerm g x tp) ps
ctxtDefUsProgs' g (UsProgExtern x tp ps) = ctxtDefUsProgs' (ctxtDefTerm g x tp) ps
ctxtDefUsProgs' g (UsProgData y cs ps) = ctxtDefUsProgs' (ctxtDeclType g y cs) ps
ctxtDefUsProgs' g (UsProgExec tm) = g

-- Populates a context with the definitions from a raw file
ctxtDefUsProgs :: UsProgs -> Ctxt
ctxtDefUsProgs = ctxtDefUsProgs' emptyCtxt
