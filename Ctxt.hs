module Ctxt where
import qualified Data.Map as Map
import Exprs

data VarDef =
    DefTerm VarScope Type
  | DefData [Ctor]

type Ctxt = Map.Map Var VarDef

emptyCtxt :: Ctxt
emptyCtxt = Map.empty

ctxtDeclTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDeclTerm g x tp = Map.insert x (DefTerm ScopeLocal tp) g

ctxtDefTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDefTerm g x tp = Map.insert x (DefTerm ScopeGlobal tp) g

ctxtDefCtor :: Ctxt -> Ctor -> Var -> Ctxt
ctxtDefCtor g (Ctor x tps) y =
  Map.insert x (DefTerm ScopeCtor (foldr TpArr (TpVar y) tps)) g

ctxtDeclType :: Ctxt -> Var -> [Ctor] -> Ctxt
ctxtDeclType g y ctors =
  foldr (\ c g -> ctxtDefCtor g c y)
    (Map.insert y (DefData ctors) g) ctors

ctxtLookupTerm :: Ctxt -> Var -> Maybe (VarScope, Type)
ctxtLookupTerm g x = Map.lookup x g >>= \ vd -> case vd of
  DefTerm sc tp -> Just (sc, tp)
  DefData cs -> Nothing

ctxtLookupType :: Ctxt -> Var -> Maybe [Ctor]
ctxtLookupType g x = Map.lookup x g >>= \ vd -> case vd of
  DefData cs -> Just cs
  _ -> Nothing

ctxtBinds :: Ctxt -> Var -> Bool
ctxtBinds = flip Map.member
