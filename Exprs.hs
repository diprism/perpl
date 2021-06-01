module Exprs where

data UsProgs =
    UsProgExec UsTm
  | UsProgFun String Type UsTm UsProgs
  | UsProgData String [Ctor] UsProgs
  deriving Show

data Progs =
    ProgExec Term
  | ProgFun String Type Term Progs
  | ProgData String [Ctor] Progs
  deriving Show

data Ctor = Ctor Var [Type]
  deriving Show

--data FnQual = FnUnr | FnAff | FnLin
--  deriving Show

type Var = String

data Dist =
    DistFail
  | DistUni
  | DistAmb
  deriving Show

data UsTm = -- User Term
    UsVar Var
  | UsLam Var Type UsTm
  | UsApp UsTm UsTm
  | UsCase UsTm [CaseUs]
  | UsSamp Dist Var
  deriving Show

data Term =
    TmVar Var Type
  | TmLam Var Type Term Type
  | TmApp Term Term Type {- -> -} Type
  | TmCase Term [Case] Var Type
  | TmSamp Dist Var
  deriving Show


data Type =
    TpArr Type Type
  | TpVar Var
--  | TpMeas Var
  deriving (Show, Eq)

--type Arg = (Var, Type)
data CaseUs = CaseUs Var [Var] UsTm
  deriving Show

data Case = Case Var [Var] Term
  deriving Show
