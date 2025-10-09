{- Code for storing information about what is in scope -}

module Scope.Ctxt where
import qualified Data.Map as Map
import Struct.Lib
import Util.Helpers

data CtTerm =
    CtDefine [Tag] [Forall] Type -- tag params, type params, type
  | CtExtern Type
  | CtCtor [Tag] [TpVar] Type   -- tag params, type params, type
  deriving Show

data CtType =
  CtData [Tag] [TpVar] [Ctor] -- tag params, type params, ctors
  deriving Show

data Ctxt = Ctxt { tpNames :: Map TpName CtType
                 , tmNames :: Map TmName CtTerm
                 , tmVars  :: Map TmVar  Type }
  deriving Show

-- Default context
emptyCtxt :: Ctxt
emptyCtxt = Ctxt Map.empty Map.empty Map.empty

-- Add a local term to the context
ctxtAddLocal :: Ctxt -> TmVar -> Type -> Ctxt
ctxtAddLocal g x tp = g{tmVars = Map.insert x tp (tmVars g)}

-- Add params to context
ctxtAddArgs :: Ctxt -> [Param] -> Ctxt
ctxtAddArgs = foldl $ uncurry . ctxtAddLocal

-- Add a global term to the context
ctxtAddDefine :: Ctxt -> TmName -> [Tag] -> [Forall] -> Type -> Ctxt
ctxtAddDefine g x tgs ps tp = g{tmNames = Map.insert x (CtDefine tgs ps tp) (tmNames g)}

ctxtAddExtern :: Ctxt -> TmName -> Type -> Ctxt
ctxtAddExtern g x tp = g{tmNames = Map.insert x (CtExtern tp) (tmNames g)}

-- Add a constructor to the context
ctxtAddCtor :: Ctxt -> Ctor -> TpName -> [Tag] -> [TpVar] -> Ctxt
ctxtAddCtor g (Ctor x tps) y tgs ps =
  let tp = joinArrows tps (TpData y tgs (TpVar <$> ps)) in
  g{tmNames = Map.insert x (CtCtor tgs ps tp) (tmNames g)}

-- Add a datatype definition to the context,
-- and all its constructors
ctxtAddData :: Ctxt -> TpName -> [Tag] -> [TpVar] -> [Ctor] -> Ctxt
ctxtAddData g y tgs ps ctors =
  foldr (\ c g -> ctxtAddCtor g c y tgs ps)
    g{tpNames = Map.insert y (CtData tgs ps ctors) (tpNames g)} ctors
  
-- Lookup a (global) term in the context
ctxtLookupTerm :: Ctxt -> TmName -> Maybe Type
ctxtLookupTerm g x = Map.lookup x (tmNames g) >>= \ dt -> case dt of
    CtDefine [] [] tp -> Just tp
    CtExtern       tp -> Just tp
    CtCtor   [] [] tp -> Just tp
    -- better use only for monomorphized code
    _ -> error "this shouldn't happen"

-- Lookup a datatype in the context
ctxtLookupType :: Ctxt -> TpName -> Maybe [Ctor]
ctxtLookupType g x = Map.lookup x (tpNames g) >>= \ dt -> case dt of
    CtData [] [] cs -> Just cs
    -- better use only for monomorphized code
    _ -> error "this shouldn't happen"

ctxtLookupType2 :: Ctxt -> TpName -> Maybe ([Tag], [TpVar], [Ctor])
ctxtLookupType2 g x = Map.lookup x (tpNames g) >>= \ dt -> case dt of
    CtData tgs ps cs -> Just (tgs, ps, cs)

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
