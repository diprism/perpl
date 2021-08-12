module Exprs where

data UsProgs =
    UsProgExec UsTm
  | UsProgFun String Type UsTm UsProgs
  | UsProgExtern String Type UsProgs
  | UsProgData String [Ctor] UsProgs

data Prog = ProgFun Var [(Var, Type)] Term Type | ProgExtern Var String [Type] Type | ProgData Var [Ctor]
data Progs = Progs [Prog] Term

data Ctor = Ctor Var [Type]

type Var = String

type Param = (Var, Type)
type Arg = (Term, Type)

data Dist =
    DistFail
  | DistUni
  | DistAmb

data UsTm = -- User Term
    UsVar Var
  | UsLam Var Type UsTm
  | UsApp UsTm UsTm
  | UsCase UsTm [CaseUs]
  | UsSamp Dist Type
  | UsLet Var UsTm UsTm

data GlobalVar = CtorVar | DefVar
  deriving Eq

data Term =
    TmVarL Var Type -- Local var
  | TmVarG GlobalVar Var [Arg] Type -- Global var
  | TmLam Var Type Term Type
  | TmApp Term Term Type {- -> -} Type
  | TmLet Var Term Type Term Type
  | TmCase Term Var [Case] Type
  | TmSamp Dist Type
  | TmAmb [Term] Type

data Type =
    TpArr Type Type
  | TpVar Var
  deriving (Eq, Ord)

data CaseUs = CaseUs Var [Var] UsTm

data Case = Case Var [Param] Term
