{- Datatypes representing PPL code structures -}

module Struct.Exprs where

import Data.String (IsString(fromString))

{- The program goes through three stages:

1. The parser produces a user-level program (UsProgs, UsTm).
2. Type inference turns it into a scheme-ified program (SProgs, Term, Type).
3. Monomorphization turns into an elaborated program (Progs, Term, Type). -}

-- User-level program
data UsProgs = UsProgs [UsProg] UsTm    -- definitions, main
  deriving (Eq, Ord)

-- Individual user-level definition
data UsProg =
    UsProgDefine TmName UsTm Type       -- lhs, rhs, type
  | UsProgExtern TmName Type            -- lhs, type
  | UsProgData TpName [TpVar] [Ctor]    -- lhs, type params, constructors
  deriving (Eq, Ord)

data Forall = Forall TpVar Bound
  deriving (Eq, Ord)
data Bound = BoundRobust | BoundNone
  deriving (Eq, Ord)

-- Scheme-ified definition
data SProg =
    SProgDefine TmName [Tag] [Forall] Term Type  -- lhs, tags, type params, rhs, type
  | SProgExtern TmName Type                     -- lhs, type
  | SProgData TpName [Tag] [TpVar] [Ctor]       -- lhs, tags, type params, constructors
  deriving (Eq, Ord)

-- Scheme-ified program
data SProgs = SProgs [SProg] Term       -- definitions, main
  deriving (Eq, Ord)

-- Elaborated definition
data Prog =
    ProgDefine TmName [Param] Term Type -- lhs, params, rhs, return type
  | ProgExtern TmName [Type] Type       -- lhs, param types, return type
  | ProgData TpName [Ctor]              -- lhs, constructors
  deriving (Eq, Ord)

-- Elaborated program
data Progs = Progs [Prog] Term          -- definitions, main
  deriving (Eq, Ord)

-- Constructor
data Ctor = Ctor TmName [Type]          -- ctor name, param types
  deriving (Eq, Ord)

-- Variable
newtype TmVar  = TmV String deriving (Eq, Ord) -- bound by lambda
newtype TmName = TmN String deriving (Eq, Ord) -- bound by define, extern, data rhs ctors
newtype TpVar  = TpV String deriving (Eq, Ord) -- bound by data lhs
newtype TpName = TpN String deriving (Eq, Ord) -- bound by data
newtype Tag    = Tag String deriving (Eq, Ord) -- bound by data lhs implicitly

instance IsString TmVar  where fromString = TmV
instance IsString TmName where fromString = TmN
instance IsString TpVar  where fromString = TpV
instance IsString TpName where fromString = TpN
instance IsString Tag    where fromString = Tag

-- Coerce between TmVar and TmName during type checking and substitution
tmVarToName :: TmVar -> TmName
tmVarToName (TmV s) = TmN s
tmNameToVar :: TmName -> TmVar
tmNameToVar (TmN s) = TmV s

-- Param is (x : tp)
type Param = (TmVar, Type)
-- Arg is (tm : tp)
type Arg = (Term, Type)

-- User-level term
data UsTm = 
    UsVar TmVar                            -- x
  | UsLam TmVar Type UsTm                  -- \ x : tp. tm
  | UsApp UsTm UsTm                        -- tm1 tm2
  | UsCase UsTm [CaseUs]                   -- case tm of case*
  | UsLet TmVar UsTm UsTm                  -- let x = tm1 in tm2
  | UsAmb [UsTm]                           -- amb tm1 tm2 ... tmn
  | UsFactorDouble Double UsTm             -- factor wt in tm (if wt is not a natural number)
  | UsFactorNat Int UsTm                   -- factor wt in tm (if wt is a natural number)
  | UsFactorRatio Rational UsTm            -- factor wt in tm (if wt is a rational number)
  | UsFail Type                            -- fail : tp
  | UsProd AddMult [UsTm]                  -- (tm1, ..., tmn)/<tm1, ..., tmn>
  | UsElimMultiplicative UsTm [TmVar] UsTm -- let (x,y,z) = tm1 in tm2
  | UsElimAdditive UsTm Int Int TmVar UsTm -- let <_,y,_> = tm1 in tm2
  | UsTmBool Bool                          -- True / False
  | UsIf UsTm UsTm UsTm                    -- if tm1 then tm2 else tm3
  | UsEqs [UsTm]                           -- tm1 == tm2 == ...
  deriving (Eq, Ord)

data Global = GlDefine | GlExtern | GlCtor
  deriving (Eq, Ord, Show)

-- With the exception of TmLam, the Type at the end of a constructor
-- below is the type of that expression as a whole
data Term =
    TmVarL TmVar Type                             -- Local var
  | TmVarG Global TmName [Tag] [Type] [Arg] Type  -- Global var app: x [tg1] ... [ti1] ... arg1 ...
  | TmLam TmVar Type Term Type                    -- \ x : tp1. tm : tp2
  | TmApp Term Term Type {- -> -} Type            -- (tm1 : (tp1 -> tp2)) (tm2 : tp1) : tp2
  | TmLet TmVar Term Type Term Type               -- let x : tp1 = tm1 in tm2 : tp2
  | TmCase Term (TpName, [Tag], [Type]) [Case] Type -- (case tm : y tg1 ... a1 ... of case1 ...) : tp
  | TmAmb [Term] Type                             -- amb tm1 tm2 ... tmn : tp
  | TmFactorDouble Double Term Type               -- factor wt in tm : tp (if wt is not a natural number)
  | TmFactorNat Int Term Type                     -- factor wt in tm : tp (if wt is a natural number)
  | TmFactorRatio Rational Term Type              -- factor wt in tm : tp (if wt is a rational number)
  | TmProd AddMult [Arg]                          -- (tm1 : tp1, tm2 : tp2, ..., tmn : tpn) / <...>
  | TmElimMultiplicative Term [Param] Term Type   -- let (x:X,y:Y,z:Z) = tm1 in tm2 : tp
  | TmElimAdditive Term Int Int Param Term Type   -- let <_..,y:Y,_..> = tm1 in tm2 : tp
  | TmEqs [Term]                                  -- tm1 == tm2 == ...
  deriving (Eq, Ord)

data AddMult = Additive | Multiplicative
  deriving (Eq, Ord)

data Type =
    TpArr Type Type                     -- function tp1 -> tp2
  | TpData TpName [Tag] [Type]          -- datatype x tg1 ... a1 ...
  | TpVar TpVar                         -- type variable
  | TpProd AddMult [Type]               -- product (tp1, ...) or <tp1, ...>
  | NoTp                                -- nothing
  deriving (Eq, Ord)

data CaseUs = CaseUs TmName [TmVar] UsTm -- | x a1 ... an -> tm
  deriving (Eq, Ord)

data Case = Case TmName [Param] Term     -- | x (a1 : tp1) ... (an : tpn) -> tm
  deriving (Eq, Ord)
