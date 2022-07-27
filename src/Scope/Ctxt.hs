{- Code for storing information about what is in scope -}

module Scope.Ctxt where
import qualified Data.Map as Map
import Struct.Lib
import Util.Helpers

data CtxtDef =
    DefTerm Scope [Var] [Var] Type -- scope, tags, params, rhs
  | DefData [Var] [Var] [Ctor]     -- tags, params, ctors
  deriving Show

type Ctxt = Map Var CtxtDef

-- Default context
emptyCtxt :: Ctxt
emptyCtxt = Map.empty

-- Add a local term to the context
ctxtDeclTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDeclTerm g x tp = Map.insert x (DefTerm ScopeLocal [] [] tp) g

-- Add params to context
ctxtDeclArgs :: Ctxt -> [Param] -> Ctxt
ctxtDeclArgs = foldl $ uncurry . ctxtDeclTerm

-- Add a global term to the context
ctxtDefTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDefTerm g x tp = Map.insert x (DefTerm ScopeGlobal [] [] tp) g

ctxtDefSTerm :: Ctxt -> Var -> Scheme -> Ctxt
ctxtDefSTerm g x (Forall tgs ps tp) = Map.insert x (DefTerm ScopeGlobal tgs ps tp) g

-- Add a constructor to the context
ctxtDefCtor :: Ctxt -> Ctor -> Var -> [Var] -> [Var] -> Ctxt
ctxtDefCtor g (Ctor x tps) y tgs ps =
  Map.insert x (DefTerm ScopeCtor tgs ps (joinArrows tps (TpData y (TpVar <$> (tgs ++ ps))))) g

-- Add a datatype definition to the context,
-- and all its constructors
ctxtDeclType :: Ctxt -> Var -> [Var] -> [Var] -> [Ctor] -> Ctxt
ctxtDeclType g y tgs ps ctors =
  foldr (\ c g -> ctxtDefCtor g c y tgs ps)
    (Map.insert y (DefData tgs ps ctors) g) ctors
  
-- Lookup a term in the context
ctxtLookupTerm :: Ctxt -> Var -> Maybe (Scope, Type)
ctxtLookupTerm g x = Map.lookup x g >>= \ vd -> case vd of
  DefTerm sc [] [] tp -> Just (sc, tp)
  DefTerm _ _ _ _ -> error "this shouldn't happen"
  _ -> Nothing

-- Lookup a datatype in the context
ctxtLookupType :: Ctxt -> Var -> Maybe [Ctor]
ctxtLookupType g x = Map.lookup x g >>= \ vd -> case vd of
  DefData [] [] cs -> Just cs
  DefData _ _ _ -> error "this shouldn't happen"
  _ -> Nothing

ctxtLookupType2 :: Ctxt -> Var -> Maybe ([Var], [Ctor])
ctxtLookupType2 g x = Map.lookup x g >>= \ vd -> case vd of
  DefData tgs ps cs -> Just (tgs++ps, cs)
  _ -> Nothing
  
-- Is this var bound in this context?
ctxtBinds :: Ctxt -> Var -> Bool
ctxtBinds = flip Map.member

-- Adds all definitions from a raw file to context
ctxtDefUsProg :: Ctxt -> UsProg -> Ctxt
ctxtDefUsProg g (UsProgFun x tp tm) = ctxtDefTerm g x tp
ctxtDefUsProg g (UsProgExtern x tp) = ctxtDefTerm g x tp
ctxtDefUsProg g (UsProgData y ps cs) = ctxtDeclType g y [] ps cs

-- Populates a context with the definitions from a raw file
ctxtDefUsProgs :: UsProgs -> Ctxt
ctxtDefUsProgs (UsProgs ps end) = foldl ctxtDefUsProg emptyCtxt ps

-- Adds all definitions from a scheme-ified file to context
ctxtDefSProg :: Ctxt -> SProg -> Ctxt
ctxtDefSProg g (SProgFun x stp tm) = ctxtDefSTerm g x stp
ctxtDefSProg g (SProgExtern x ps tp) = ctxtDefTerm g x (joinArrows ps tp)
ctxtDefSProg g (SProgData y tgs ps cs) = ctxtDeclType g y tgs ps cs

-- Populates a context with the definitions from a scheme-ified file
ctxtDefSProgs :: SProgs -> Ctxt
ctxtDefSProgs (SProgs ps end) = foldl ctxtDefSProg emptyCtxt ps

-- Adds all definitions from a file to context
ctxtDefProg :: Ctxt -> Prog -> Ctxt
ctxtDefProg g (ProgFun x ps tm tp) = ctxtDefTerm g x (joinArrows (map snd ps) tp)
ctxtDefProg g (ProgExtern x ps tp) = ctxtDefTerm g x (joinArrows ps tp)
ctxtDefProg g (ProgData y cs) = ctxtDeclType g y [] [] cs

-- Populates a context with the definitions from a file
ctxtDefProgs :: Progs -> Ctxt
ctxtDefProgs (Progs ps end) = foldl ctxtDefProg emptyCtxt ps

