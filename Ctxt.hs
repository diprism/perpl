module Ctxt where
import qualified Data.Map as Map
import Exprs

type TermCtxt = Map.Map Var Type
type TypeCtxt = Map.Map Var [Ctor]

data Ctxt = Ctxt TermCtxt TypeCtxt

emptyCtxt :: Ctxt
emptyCtxt = Ctxt Map.empty Map.empty

ctxtDeclTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDeclTerm (Ctxt tmc tpc) x tp = Ctxt (Map.insert x tp tmc) tpc

ctxtDeclType :: Ctxt -> Var -> [Ctor] -> Ctxt
ctxtDeclType (Ctxt tmc tpc) y ctors =
  Ctxt
    (foldr (\ (Ctor x tps) -> Map.insert x (foldr TpArr (TpVar y) tps)) tmc ctors)
    (Map.insert y ctors tpc)

ctxtLookupTerm :: Ctxt -> Var -> Maybe Type
ctxtLookupTerm (Ctxt tmc tpc) x = Map.lookup x tmc

ctxtLookupType :: Ctxt -> Var -> Maybe [Ctor]
ctxtLookupType (Ctxt tmc tpc) x = Map.lookup x tpc

ctxtBinds :: Ctxt -> Var -> Bool
ctxtBinds (Ctxt tmc tpc) x = Map.member x tmc || Map.member x tpc
