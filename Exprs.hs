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
  | TmCase Term Type [Case] Type
  | TmSamp Dist Type
  | TmAmb [Term] Type

data Type =
    TpArr Type Type
  | TpVar Var
  -- For internal use only
  | TpMaybe Type
  | TpBool
--  | TpMeas Var
  deriving Eq

data CaseUs = CaseUs Var [Var] UsTm

data Case = Case Var [Param] Term

tpMaybeName   = "%Maybe%"
tpBoolName    = "%Bool%"
tmNothingName = "%nothing%"
tmJustName    = "%just%"
tmTrueName    = "%true%"
tmFalseName   = "%false%"

tmMaybe :: Maybe Term -> Type -> Term
tmMaybe Nothing tp = TmVarG CtorVar tmNothingName [] (TpMaybe tp)
tmMaybe (Just tm) tp = TmVarG CtorVar tmJustName [(tm, tp)] (TpMaybe tp)
tmElimMaybe :: Term -> Type -> Term -> (Var, Term) -> Type -> Term
tmElimMaybe tm tp ntm (jx, jtm) tp' =
  TmCase tm (TpMaybe tp) [Case tmNothingName [] ntm, Case tmJustName [(jx, tp)] jtm] tp'
tmBool :: Bool -> Term
tmBool b = TmVarG CtorVar (if b then tmTrueName else tmFalseName) [] TpBool
tmIf :: Term -> Term -> Term -> Type -> Term
tmIf iftm thentm elsetm tp =
  TmCase iftm TpBool [Case tmFalseName [] elsetm, Case tmTrueName [] thentm] tp

boolCtors = [Ctor tmFalseName [], Ctor tmTrueName []]
maybeCtors tp = [Ctor tmNothingName [], Ctor tmJustName [tp]]

