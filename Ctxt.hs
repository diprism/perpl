module Ctxt where
import qualified Data.Map as Map
import Exprs

data VarDef =
    DefTerm Type      -- Global fun
  | DeclTerm Type     -- Local term
  | DefData [Ctor]    -- Data def

type Ctxt = Map.Map Var VarDef

emptyCtxt :: Ctxt
emptyCtxt = Map.empty

ctxtDeclTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDeclTerm g x tp = Map.insert x (DeclTerm tp) g

ctxtDefTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDefTerm g x tp = Map.insert x (DefTerm tp) g

ctxtDeclType :: Ctxt -> Var -> [Ctor] -> Ctxt
ctxtDeclType g y ctors =
  foldr
    (\ (Ctor x tps) -> Map.insert x (DefTerm (foldr TpArr (TpVar y) tps)))
    (Map.insert y (DefData ctors) g) ctors

ctxtLookupTerm :: Ctxt -> Var -> Maybe Type
ctxtLookupTerm g x = Map.lookup x g >>= \ vd -> case vd of
  DefTerm tp -> Just tp
  DeclTerm tp -> Just tp
  DefData cs -> Nothing

ctxtIsGlobal :: Ctxt -> Var -> Bool
ctxtIsGlobal g x = flip (maybe False) (Map.lookup x g) $ \ vd -> case vd of
  DefTerm tp -> True
  DeclTerm tp -> False
  DefData cs -> True

ctxtLookupType :: Ctxt -> Var -> Maybe [Ctor]
ctxtLookupType g x = Map.lookup x g >>= \ vd -> case vd of
  DefData cs -> Just cs
  _ -> Nothing

ctxtBinds :: Ctxt -> Var -> Bool
ctxtBinds = flip Map.member
