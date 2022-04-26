{- Code for storing information about what is in scope -}
-- TODO: merge with Env (in src/TypeInf.hs)

module Ctxt where
import qualified Data.Map as Map
import Exprs
import Util.Helpers
import Struct
import Show()

data CtxtDef =
    DefTerm Scope Type
  | DefData [Ctor]
  deriving Show

type Ctxt = Map Var CtxtDef

-- Default context
emptyCtxt :: Ctxt
emptyCtxt = Map.empty

-- Add a local term to the context
ctxtDeclTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDeclTerm g x tp = Map.insert x (DefTerm ScopeLocal tp) g

-- Add params to context
ctxtDeclArgs :: Ctxt -> [Param] -> Ctxt
ctxtDeclArgs = foldl $ uncurry . ctxtDeclTerm

-- Add a global term to the context
ctxtDefTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDefTerm g x tp = Map.insert x (DefTerm ScopeGlobal tp) g

-- Add a constructor to the context
ctxtDefCtor :: Ctxt -> Ctor -> Var -> [Var] -> Ctxt
ctxtDefCtor g (Ctor x tps) y ps =
  Map.insert x (DefTerm ScopeCtor (foldr TpArr (TpVar y [TpVar x [] | x <- ps]) tps)) g

-- Add a datatype definition to the context,
-- and all its constructors
ctxtDeclType :: Ctxt -> Var -> [Var] -> [Ctor] -> Ctxt
ctxtDeclType g y ps ctors =
  foldr (\ c g -> ctxtDefCtor g c y ps)
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
ctxtDefProg g (ProgExtern x ps tp) = ctxtDefTerm g x (joinArrows ps tp)
ctxtDefProg g (ProgData y cs) = ctxtDeclType g y [] cs

-- Populates a context with the definitions from a file
ctxtDefProgs :: Progs -> Ctxt
ctxtDefProgs (Progs ps end) = foldl ctxtDefProg emptyCtxt ps

-- Adds all definitions from a raw file to context
ctxtDefUsProg :: Ctxt -> UsProg -> Ctxt
ctxtDefUsProg g (UsProgFun x tp tm) = ctxtDefTerm g x tp
ctxtDefUsProg g (UsProgExtern x tp) = ctxtDefTerm g x tp
ctxtDefUsProg g (UsProgData y ps cs) = ctxtDeclType g y ps cs

-- Populates a context with the definitions from a raw file
ctxtDefUsProgs :: UsProgs -> Ctxt
ctxtDefUsProgs (UsProgs ps end) = foldl ctxtDefUsProg emptyCtxt ps
