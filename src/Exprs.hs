module Exprs where

data UsProgs = UsProgs [UsProg] UsTm
  deriving (Eq, Ord)

data UsProg =
    UsProgFun String Type UsTm
  | UsProgExtern String Type
  | UsProgData String [Ctor]
  deriving (Eq, Ord)

data Prog =
    ProgFun Var [(Var, Type)] Term Type
  | ProgExtern Var String [Type] Type
  | ProgData Var [Ctor]
  deriving (Eq, Ord)

data Progs = Progs [Prog] Term
  deriving (Eq, Ord)

data SProg =
    SProgFun Var Scheme Term
  | SProgExtern Var [Type] Type
  | SProgData Var [Ctor]
  deriving (Eq, Ord)

data SProgs = SProgs [SProg] Term
  deriving (Eq, Ord)

data Ctor = Ctor Var [Type]
  deriving (Eq, Ord)

type Var = String

type Param = (Var, Type)
type Arg = (Term, Type)

data Scheme = Forall [Var] Type
  deriving (Eq, Ord)

data Dist =
    DistFail
  | DistUni
  | DistAmb
  deriving (Eq, Ord)

data UsTm = -- User Term
    UsVar Var
  | UsLam Var Type UsTm
  | UsApp UsTm UsTm
  | UsCase UsTm [CaseUs]
  | UsSamp Dist Type
  | UsLet Var Type UsTm UsTm
  | UsAmb [UsTm]
  | UsProd AddMult [UsTm]
  | UsElimProd AddMult UsTm [Var] UsTm
  | UsTmBool Bool
  | UsIf UsTm UsTm UsTm
  | UsEqs [UsTm]
  deriving (Eq, Ord)

data GlobalVar = CtorVar | DefVar
  deriving (Eq, Ord)

data Term =
    TmVarL Var Type -- Local var
  | TmVarG GlobalVar Var [Type] [Arg] Type -- Global var
  | TmLam Var Type Term Type
  | TmApp Term Term Type {- -> -} Type
  | TmLet Var Term Type Term Type
  | TmCase Term Var [Case] Type
  | TmSamp Dist Type
  | TmAmb [Term] Type
  | TmProd AddMult [Arg]
  | TmElimProd AddMult Term [Param] Term Type
  | TmEqs [Term]
  deriving (Eq, Ord)

data AddMult = Additive | Multiplicative
  deriving (Eq, Ord)

data Type =
    TpArr Type Type
  | TpVar Var
  | TpProd AddMult [Type]
  | NoTp
  deriving (Eq, Ord)

data CaseUs = CaseUs Var [Var] UsTm
  deriving (Eq, Ord)

data Case = Case Var [Param] Term
  deriving (Eq, Ord)
