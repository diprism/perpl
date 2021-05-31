module Ctxt where
import qualified Data.Map as Map
import Exprs

type TermCtxt = Map.Map Var Type
type TypeCtxt = Map.Map Var [Ctor]

data Ctxt = Ctxt TermCtxt TypeCtxt

ctxtDeclTerm :: Ctxt -> Var -> Type -> Ctxt
ctxtDeclTerm (Ctxt tmc tpc) x tp = Ctxt (Map.insert x tp tmc) tpc

ctxtDeclType :: Ctxt -> Var -> [Ctor] -> Ctxt
ctxtDeclType (Ctxt tmc tpc) x ctors = Ctxt tmc (Map.insert x ctors tpc)

ctxtLookupTerm :: Ctxt -> Var -> Maybe Type
ctxtLookupTerm (Ctxt tmc tpc) x = Map.lookup x tmc

ctxtLookupType :: Ctxt -> Var -> Maybe [Ctor]
ctxtLookupType (Ctxt tmc tpc) x = Map.lookup x tpc

