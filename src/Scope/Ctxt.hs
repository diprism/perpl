{- Code for storing information about what is in scope -}

module Scope.Ctxt where
import qualified Data.Map as Map
import Struct.Lib
import Util.Helpers

data CtxtDef =
    CtTerm CtTerm
  | CtType CtType
  deriving Show

data CtTerm =
    CtLocal Type
  | CtDefine [Var] [Forall] Type -- tags, type params, type
  | CtExtern Type
  | CtCtor [Var] [Var] Type   -- tags, type params, type
  deriving Show

data CtType =
  CtData [Var] [Var] [Ctor] -- tags, type params, ctors
  -- CtTypeVar -- not currently used
  deriving Show

type Ctxt = Map Var CtxtDef

-- Default context
emptyCtxt :: Ctxt
emptyCtxt = Map.empty

-- Add a local term to the context
ctxtAddLocal :: Ctxt -> Var -> Type -> Ctxt
ctxtAddLocal g x tp = Map.insert x (CtTerm (CtLocal tp)) g

-- Add params to context
ctxtAddArgs :: Ctxt -> [Param] -> Ctxt
ctxtAddArgs = foldl $ uncurry . ctxtAddLocal

-- Add a global term to the context
ctxtAddDefine :: Ctxt -> Var -> [Var] -> [Forall] -> Type -> Ctxt
ctxtAddDefine g x tgs ps tp = Map.insert x (CtTerm (CtDefine tgs ps tp)) g

ctxtAddExtern :: Ctxt -> Var -> Type -> Ctxt
ctxtAddExtern g x tp = Map.insert x (CtTerm (CtExtern tp)) g

-- Add a constructor to the context
ctxtAddCtor :: Ctxt -> Ctor -> Var -> [Var] -> [Var] -> Ctxt
ctxtAddCtor g (Ctor x tps) y tgs ps =
  let tp = joinArrows tps (TpData y (TgVar <$> tgs) (TpVar <$> ps)) in
  Map.insert x (CtTerm (CtCtor tgs ps tp)) g

-- Add a datatype definition to the context,
-- and all its constructors
ctxtAddData :: Ctxt -> Var -> [Var] -> [Var] -> [Ctor] -> Ctxt
ctxtAddData g y tgs ps ctors =
  foldr (\ c g -> ctxtAddCtor g c y tgs ps)
    (Map.insert y (CtType (CtData tgs ps ctors)) g) ctors
  
-- Lookup a term in the context
ctxtLookupTerm :: Ctxt -> Var -> Maybe Type
ctxtLookupTerm g x = Map.lookup x g >>= \ d -> case d of
  CtTerm dt -> case dt of
    CtLocal tp -> Just tp
    CtDefine [] [] tp -> Just tp
    CtCtor [] [] tp -> Just tp
    CtExtern tp -> Just tp
    _ -> error "this shouldn't happen"
  CtType _ -> Nothing

-- Lookup a datatype in the context
ctxtLookupType :: Ctxt -> Var -> Maybe [Ctor]
ctxtLookupType g x = Map.lookup x g >>= \ d -> case d of
  CtTerm _ -> Nothing
  CtType dt -> case dt of
    CtData [] [] cs -> Just cs
    _ -> error "this shouldn't happen"

ctxtLookupType2 :: Ctxt -> Var -> Maybe ([Var], [Var], [Ctor])
ctxtLookupType2 g x = Map.lookup x g >>= \ d -> case d of
  CtTerm _ -> Nothing
  CtType dt -> case dt of
    CtData tgs ps cs -> Just (tgs, ps, cs)
  
-- Is this var bound in this context?
ctxtBinds :: Ctxt -> Var -> Bool
ctxtBinds = flip Map.member

-- Adds all definitions from a raw file to context
ctxtAddUsProg :: Ctxt -> UsProg -> Ctxt
ctxtAddUsProg g (UsProgDefine x tm tp) = ctxtAddDefine g x [] [] tp
ctxtAddUsProg g (UsProgExtern x tp) = ctxtAddExtern g x tp
ctxtAddUsProg g (UsProgData y ps cs) = ctxtAddData g y [] ps cs

-- Populates a context with the definitions from a raw file
ctxtAddUsProgs :: UsProgs -> Ctxt
ctxtAddUsProgs (UsProgs ps end) = foldl ctxtAddUsProg emptyCtxt ps

-- Adds all definitions from a scheme-ified file to context
ctxtAddSProg :: Ctxt -> SProg -> Ctxt
ctxtAddSProg g (SProgDefine x tgs ps tm tp) = ctxtAddDefine g x tgs ps tp
ctxtAddSProg g (SProgExtern x tp) = ctxtAddExtern g x tp
ctxtAddSProg g (SProgData y tgs ps cs) = ctxtAddData g y tgs ps cs

-- Populates a context with the definitions from a scheme-ified file
ctxtAddSProgs :: SProgs -> Ctxt
ctxtAddSProgs (SProgs ps end) = foldl ctxtAddSProg emptyCtxt ps

-- Adds all definitions from a file to context
ctxtAddProg :: Ctxt -> Prog -> Ctxt
ctxtAddProg g (ProgDefine x ps tm tp) = ctxtAddDefine g x [] [] (joinArrows (map snd ps) tp)
ctxtAddProg g (ProgExtern x ps tp) = ctxtAddExtern g x (joinArrows ps tp)
ctxtAddProg g (ProgData y cs) = ctxtAddData g y [] [] cs

-- Populates a context with the definitions from a file
ctxtAddProgs :: Progs -> Ctxt
ctxtAddProgs (Progs ps end) = foldl ctxtAddProg emptyCtxt ps
