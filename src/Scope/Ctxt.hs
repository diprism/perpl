{- Code for storing information about what is in scope -}

module Scope.Ctxt where
import qualified Data.Map as Map
import Struct.Lib
import Util.Helpers

data CtxtDef =
    DefLocal Type
  | DefGlobal [Var] [Var] Type -- tags, params, type
  | DefCtor [Var] [Var] Type   -- tags, params, type
  | DefData [Var] [Var] [Ctor] -- tags, params, ctors
  deriving Show

type Ctxt = Map Var CtxtDef

-- Default context
emptyCtxt :: Ctxt
emptyCtxt = Map.empty

-- Add a local term to the context
ctxtDefLocal :: Ctxt -> Var -> Type -> Ctxt
ctxtDefLocal g x tp = Map.insert x (DefLocal tp) g

-- Add params to context
ctxtDeclArgs :: Ctxt -> [Param] -> Ctxt
ctxtDeclArgs = foldl $ uncurry . ctxtDefLocal

-- Add a global term to the context
ctxtDefGlobal :: Ctxt -> Var -> [Var] -> [Var] -> Type -> Ctxt
ctxtDefGlobal g x tgs ps tp = Map.insert x (DefGlobal tgs ps tp) g

-- Add a constructor to the context
ctxtDefCtor :: Ctxt -> Ctor -> Var -> [Var] -> [Var] -> Ctxt
ctxtDefCtor g (Ctor x tps) y tgs ps =
  Map.insert x (DefCtor tgs ps (joinArrows tps (TpData y (TpVar <$> (tgs ++ ps))))) g

-- Add a datatype definition to the context,
-- and all its constructors
ctxtDefData :: Ctxt -> Var -> [Var] -> [Var] -> [Ctor] -> Ctxt
ctxtDefData g y tgs ps ctors =
  foldr (\ c g -> ctxtDefCtor g c y tgs ps)
    (Map.insert y (DefData tgs ps ctors) g) ctors
  
-- Lookup a term in the context
ctxtLookupTerm :: Ctxt -> Var -> Maybe Type
ctxtLookupTerm g x = Map.lookup x g >>= \ vd -> case vd of
  DefLocal tp -> Just tp
  DefGlobal [] [] tp -> Just tp
  DefCtor [] [] tp -> Just tp
  DefData _ _ _ -> Nothing
  _ -> error "this shouldn't happen"

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
ctxtDefUsProg g (UsProgFun x tp tm) = ctxtDefGlobal g x [] [] tp
ctxtDefUsProg g (UsProgExtern x tp) = ctxtDefGlobal g x [] [] tp
ctxtDefUsProg g (UsProgData y ps cs) = ctxtDefData g y [] ps cs

-- Populates a context with the definitions from a raw file
ctxtDefUsProgs :: UsProgs -> Ctxt
ctxtDefUsProgs (UsProgs ps end) = foldl ctxtDefUsProg emptyCtxt ps

-- Adds all definitions from a scheme-ified file to context
ctxtDefSProg :: Ctxt -> SProg -> Ctxt
ctxtDefSProg g (SProgFun x (Forall tgs ps tp) tm) = ctxtDefGlobal g x tgs ps tp
ctxtDefSProg g (SProgExtern x ps tp) = ctxtDefGlobal g x [] [] (joinArrows ps tp)
ctxtDefSProg g (SProgData y tgs ps cs) = ctxtDefData g y tgs ps cs

-- Populates a context with the definitions from a scheme-ified file
ctxtDefSProgs :: SProgs -> Ctxt
ctxtDefSProgs (SProgs ps end) = foldl ctxtDefSProg emptyCtxt ps

-- Adds all definitions from a file to context
ctxtDefProg :: Ctxt -> Prog -> Ctxt
ctxtDefProg g (ProgFun x ps tm tp) = ctxtDefGlobal g x [] [] (joinArrows (map snd ps) tp)
ctxtDefProg g (ProgExtern x ps tp) = ctxtDefGlobal g x [] [] (joinArrows ps tp)
ctxtDefProg g (ProgData y cs) = ctxtDefData g y [] [] cs

-- Populates a context with the definitions from a file
ctxtDefProgs :: Progs -> Ctxt
ctxtDefProgs (Progs ps end) = foldl ctxtDefProg emptyCtxt ps

