module Ctxt where
import qualified Data.Map as Map
import Exprs

type Ctxt = Map.Map Var (Either Type [Ctor])

emptyCtxt :: Ctxt
emptyCtxt = Map.empty

ctxtDeclTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDeclTerm g x tp = Map.insert x (Left tp) g

ctxtDeclType :: Ctxt -> Var -> [Ctor] -> Ctxt
ctxtDeclType g y ctors =
  foldr
    (\ (Ctor x tps) -> Map.insert x (Left (foldr TpArr (TpVar y) tps)))
    (Map.insert y (Right ctors) g) ctors

ctxtLookupTerm :: Ctxt -> Var -> Maybe Type
ctxtLookupTerm g x = Map.lookup x g >>= either Just (const Nothing)

ctxtLookupType :: Ctxt -> Var -> Maybe [Ctor]
ctxtLookupType g x = Map.lookup x g >>= either (const Nothing) Just

ctxtBinds :: Ctxt -> Var -> Bool
ctxtBinds = flip Map.member
