module Ctxt where
import qualified Data.Map as Map
import Exprs

data VarDef =
    DefTerm VarScope Type
  | DefData [Ctor]

type Ctxt = Map.Map Var VarDef

-- Default context
emptyCtxt :: Ctxt
emptyCtxt = Map.empty

-- Add a local term to the context
ctxtDeclTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDeclTerm g x tp = Map.insert x (DefTerm ScopeLocal tp) g

ctxtDeclArgs :: Ctxt -> [(Var, Type)] -> Ctxt
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
ctxtLookupTerm :: Ctxt -> Var -> Maybe (VarScope, Type)
ctxtLookupTerm g x = Map.lookup x g >>= \ vd -> case vd of
  DefTerm sc tp -> Just (sc, tp)
  DefData cs -> Nothing

-- Lookup a datatype in the context
ctxtLookupType :: Ctxt -> Var -> Maybe [Ctor]
ctxtLookupType g x = Map.lookup x g >>= \ vd -> case vd of
  DefData cs -> Just cs
  _ -> Nothing

ctxtLookupType' :: Ctxt -> Type -> Maybe [Ctor]
ctxtLookupType' g (TpVar y) = Map.lookup y g >>= \ vd -> case vd of
  DefData cs -> Just cs
  _ -> Nothing
ctxtLookupType' g TpBool = Just boolCtors
ctxtLookupType' g (TpMaybe tp) = Just (maybeCtors tp)

-- Is this var bound in this context?
ctxtBinds :: Ctxt -> Var -> Bool
ctxtBinds = flip Map.member
