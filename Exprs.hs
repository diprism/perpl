module Exprs where

data Progs =
    ProgRun Term
  | ProgFun String [Arg] Term Progs
  | ProgData String [Ctor] Progs
  deriving Show

data Ctor = Ctor Var [Type]
  deriving Show

data FnQual = FnUnr | FnAff | FnLin
  deriving Show

type Var = String

data Term =
    TmVar Var
  | TmLam FnQual Var Type Term
  | TmApp Term Term
  | TmLet Var Type Term Term
  | TmSamp Term
  | TmObs Term Term
  | TmFail
  | TmCase Term [Case]
  | TmAmb
  deriving Show

data Type =
    TpArr Type FnQual Type
  | TpVar Var
  deriving Show

type Arg = (Var, Type)
data Case = Case Var [Var] Term
  deriving Show
