{- Datatypes representing PPL code structures -}

module Struct.Exprs where

-- User-level program
data UsProgs = UsProgs [UsProg] UsTm
  deriving (Eq, Ord)

-- Individual user-level defnition
data UsProg =
    UsProgFun String Type UsTm
  | UsProgExtern String Type
  | UsProgData String [Var] [Ctor]
  deriving (Eq, Ord)

-- Elaborated definition
data Prog =
    ProgFun Var [(Var, Type)] Term Type
  | ProgExtern Var [Type] Type
  | ProgData Var [Ctor]
  deriving (Eq, Ord)

-- Elaborated program
data Progs = Progs [Prog] Term
  deriving (Eq, Ord)

-- Scheme-ified definition
data SProg =
    SProgFun Var Scheme Term
  | SProgExtern Var [Type] Type
  | SProgData Var [Var] {- tags -} [Var] {- params -} [Ctor]
  deriving (Eq, Ord)

-- Scheme-ified program
data SProgs = SProgs [SProg] Term
  deriving (Eq, Ord)

-- Constructor
data Ctor = Ctor Var [Type]
  deriving (Eq, Ord)

-- Variable
type Var = String

-- Param is (x : tp)
type Param = (Var, Type)
-- Arg is (tm : tp)
type Arg = (Term, Type)

type IsTag = Bool

--                   tags params type
data Scheme = Forall [Var] [Var] Type
  deriving (Eq, Ord)

-- Different kinds of supported distributions
data Dist =
    DistFail
  | DistUni
  | DistAmb
  deriving (Eq, Ord)

data UsTm = -- User-level Term
    UsVar Var -- x
  | UsLam Var Type UsTm                -- \ x : tp. tm
  | UsApp UsTm UsTm                    -- tm1 tm2
  | UsCase UsTm [CaseUs]               -- case tm of case*
  | UsSamp Dist Type                   -- sample fail/uniform/amb : tp
  | UsLet Var Type UsTm UsTm           -- let x : tp = tm1 in tm2
  | UsAmb [UsTm]                       -- amb tm1 tm2 ... tmn
  | UsProd AddMult [UsTm]              -- (tm1, ..., tmn)/<tm1, ..., tmn>
  | UsElimProd AddMult UsTm [Var] UsTm -- let (x,y,z)/<x,y,z> = tm1 in tm2
  | UsTmBool Bool                      -- True / False
  | UsIf UsTm UsTm UsTm                -- if tm1 then tm2 else tm3
  | UsEqs [UsTm]                       -- tm1 == tm2 == ...
  deriving (Eq, Ord)

data GlobalVar = CtorVar | DefVar
  deriving (Eq, Ord)

-- Which kind of var: local function, global function, or constructor
data Scope = ScopeLocal | ScopeGlobal | ScopeCtor
  deriving (Eq, Show)

-- For the most part, the Type at the end of a constructor
-- below is the type of that expression as a whole
data Term =
    TmVarL Var Type                           -- Local var
  | TmVarG GlobalVar Var [Type] [Arg] Type    -- Global var
  | TmLam Var Type Term Type                  -- \ x : tp1. tm : tp2
  | TmApp Term Term Type {- -> -} Type        -- (tm1 : (tp1 -> tp2)) (tm2  : tp1) : tp2
  | TmLet Var Term Type Term Type             -- let x : tp1 = tm1 in tp2 : tp2
  | TmCase Term (Var, [Type]) [Case] Type     -- (case tm : y [tis] of case*) : tp
  | TmSamp Dist Type                          -- sample fail/uniform/amb : tp
  | TmAmb [Term] Type                         -- amb tm1 tm2 ... tmn : tp
  | TmProd AddMult [Arg]                      -- (tm1 : tp1, tm2 : tp2, ..., tmn : tpn) / <...>
  | TmElimProd AddMult Term [Param] Term Type -- let (x:X,y:Y,z:Z)/<...> = tm1 in tm2 : tp
  | TmEqs [Term]                              -- tm1 == tm2 == ...
  deriving (Eq, Ord)

data AddMult = Additive | Multiplicative
  deriving (Eq, Ord)

data Type =
    TpArr Type Type -- tp1 -> tp2
  | TpVar Var [Type] -- y [type instance args (tis)]
  | TpProd AddMult [Type] -- (tp1 */& tp2 */& ... */& tpn)
  | NoTp -- nothing
  deriving (Eq, Ord)

data CaseUs = CaseUs Var [Var] UsTm --- | x a1 a2 ... an -> tm
  deriving (Eq, Ord)

data Case = Case Var [Param] Term --- | x (a1 : tp1) (a2 : tp2) ... (an : tpn) -> tm
  deriving (Eq, Ord)
