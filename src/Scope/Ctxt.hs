{- Code for storing information about what is in scope -}
{-# LANGUAGE StandaloneDeriving #-}

module Scope.Ctxt where
import qualified Data.Map as Map
import Data.Foldable (toList)
import Struct.Lib
import Util.None
import Util.Helpers

data CtxtDef tags tparams dparams =
    DefLocalTerm (Type dparams)
  | DefGlobalTerm (tags Var) (tparams Var) (Type dparams)
  | DefCtorTerm (tags Var) (tparams Var) (Type dparams)
  | DefData (tags Var) (dparams Var) [Ctor dparams]

type Ctxt tags tparams dparams = Map Var (CtxtDef tags tparams dparams)

-- Default context
emptyCtxt :: Ctxt tags tparams dparams
emptyCtxt = Map.empty

-- Add a local term to the context
ctxtDeclTerm :: Ctxt tags tparams dparams -> Var -> Type dparams -> Ctxt tags tparams dparams
ctxtDeclTerm g x tp = Map.insert x (DefLocalTerm tp) g

-- Add params to context
ctxtDeclArgs :: Ctxt tags tparams dparams -> [Param dparams] -> Ctxt tags tparams dparams
ctxtDeclArgs = foldl $ uncurry . ctxtDeclTerm

-- Add a global term to the context
ctxtDefTerm :: Ctxt None None dparams -> Var -> Type dparams -> Ctxt None None dparams
ctxtDefTerm g x tp = Map.insert x (DefGlobalTerm None None tp) g

ctxtDefSTerm :: Ctxt [] [] [] -> Var -> Scheme -> Ctxt [] [] []
ctxtDefSTerm g x (Forall tags tparams tp) = Map.insert x (DefGlobalTerm tags tparams tp) g

-- Add a constructor to the context
ctxtDefCtor :: Functor dparams => Ctxt None None dparams -> Ctor dparams -> Var -> dparams Var -> Ctxt None None dparams
ctxtDefCtor g (Ctor x tps) y ps =
  Map.insert x (DefCtorTerm None None (joinArrows tps (TpData y (TpVar <$> ps)))) g
  
ctxtDefSCtor :: Ctxt [] [] [] -> Ctor [] -> Var -> [Var] -> [Var] -> Ctxt [] [] []
ctxtDefSCtor g (Ctor x tps) y tgs ps =
  Map.insert x (DefCtorTerm tgs ps (joinArrows tps (TpData y (TpVar <$> (tgs ++ ps))))) g

-- Add a datatype definition to the context,
-- and all its constructors
-- TODO: instead of storing DefCtorTerm, is it better to look inside DefData at lookup time?
ctxtDeclType :: Functor dparams => Ctxt None None dparams -> Var -> dparams Var -> [Ctor dparams] -> Ctxt None None dparams
ctxtDeclType g y ps ctors =
  foldr (\ c g -> ctxtDefCtor g c y ps)
    (Map.insert y (DefData None ps ctors) g) ctors

ctxtDeclSType :: Ctxt [] [] [] -> Var -> [Var] -> [Var] -> [Ctor []] -> Ctxt [] [] []
ctxtDeclSType g y tgs ps ctors =
  foldr (\ c g -> ctxtDefSCtor g c y tgs ps)
    (Map.insert y (DefData tgs ps ctors) g) ctors
  
-- Lookup a term in the context
ctxtLookupTerm :: Ctxt None None dparams -> Var -> Maybe (Scope, Type dparams)
ctxtLookupTerm g x = Map.lookup x g >>= \ vd -> case vd of
  DefLocalTerm            tp -> Just (ScopeLocal,  tp)
  DefGlobalTerm None None tp -> Just (ScopeGlobal, tp)
  DefCtorTerm   None None tp -> Just (ScopeCtor,   tp)
  DefData _ _ _              -> Nothing

-- Lookup a datatype in the context
ctxtLookupType :: Ctxt None tparams None -> Var -> Maybe [Ctor None]
ctxtLookupType g x = Map.lookup x g >>= \ vd -> case vd of
  DefData None None cs -> Just cs
  _ -> Nothing

ctxtLookupType2 :: (Foldable tags, Foldable dparams) => Ctxt tags tparams dparams -> Var -> Maybe ([Var], [Ctor dparams])
ctxtLookupType2 g x = Map.lookup x g >>= \ vd -> case vd of
  DefData tgs ps cs -> Just (toList tgs ++ toList ps, cs)
  _ -> Nothing
  
-- Is this var bound in this context?
ctxtBinds :: Ctxt tags tparams dparams -> Var -> Bool
ctxtBinds = flip Map.member

-- Adds all definitions from a raw file to context
ctxtDefUsProg :: Ctxt None None [] -> UsProg -> Ctxt None None []
ctxtDefUsProg g (UsProgFun x tp tm) = ctxtDefTerm g x tp
ctxtDefUsProg g (UsProgExtern x tp) = ctxtDefTerm g x tp
ctxtDefUsProg g (UsProgData y ps cs) = ctxtDeclType g y ps cs

-- Populates a context with the definitions from a raw file
ctxtDefUsProgs :: UsProgs -> Ctxt None None []
ctxtDefUsProgs (UsProgs ps end) = foldl ctxtDefUsProg emptyCtxt ps

-- Adds all definitions from a scheme-ified file to context
ctxtDefSProg :: Ctxt [] [] [] -> SProg -> Ctxt [] [] []
ctxtDefSProg g (SProgFun x stp tm) = ctxtDefSTerm g x stp
ctxtDefSProg g (SProgExtern x ps tp) = ctxtDefSTerm g x (Forall [] [] (joinArrows ps tp))
ctxtDefSProg g (SProgData y tgs ps cs) = ctxtDeclSType g y tgs ps cs

-- Populates a context with the definitions from a scheme-ified file
ctxtDefSProgs :: SProgs -> Ctxt [] [] []
ctxtDefSProgs (SProgs ps end) = foldl ctxtDefSProg emptyCtxt ps

-- Adds all definitions from a file to context
ctxtDefProg :: Ctxt None None None -> Prog -> Ctxt None None None
ctxtDefProg g (ProgFun x ps tm tp) = ctxtDefTerm g x (joinArrows (map snd ps) tp)
ctxtDefProg g (ProgExtern x ps tp) = ctxtDefTerm g x (joinArrows ps tp)
ctxtDefProg g (ProgData y cs) = ctxtDeclType g y None cs

-- Populates a context with the definitions from a file
ctxtDefProgs :: Progs -> Ctxt None None None
ctxtDefProgs (Progs ps end) = foldl ctxtDefProg emptyCtxt ps

