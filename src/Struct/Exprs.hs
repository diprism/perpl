{- Datatypes representing PPL code structures -}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

module Struct.Exprs where

import Util.None
import Data.Foldable (toList)

{- The program goes through three stages:

1. The parser produces a user-level program (UsProgs, UsTm, UsTp).
2. Type inference turns it into a scheme-ified program (SProgs, Term, Type/Scheme).
3. Monomorphization turns into an elaborated program (Progs, Term, Type). -}

-- User-level program
data UsProgs = UsProgs [UsProg] (UsTm []) -- definitions, main
  deriving (Eq, Ord)

-- Individual user-level definition
data UsProg =
    UsProgFun Var (Type []) (UsTm [])   -- lhs, type, rhs
  | UsProgExtern Var (Type [])          -- lhs, type
  | UsProgData Var [Var] [Ctor []]      -- lhs, type params, constructors
  deriving (Eq, Ord)

-- Scheme-ified definition
data SProg =
    SProgFun Var Scheme (Term [])       -- lhs, type, rhs
  | SProgExtern Var [Type []] (Type []) -- lhs, param types, return type
  | SProgData Var [Var] [Var] [Ctor []] -- lhs, tags, type params, constructors
  deriving (Eq, Ord)

-- Scheme-ified program
data SProgs = SProgs [SProg] (Term [])  -- definitions, main
  deriving (Eq, Ord)

-- Elaborated definition
data Prog =
    ProgFun Var [(Var, Type None)] (Term None) (Type None) -- lhs, params, rhs, return type
  | ProgExtern Var [Type None] (Type None)                 -- lhs, param types, return type
  | ProgData Var [Ctor None]                               -- lhs, type params, constructors
  deriving (Eq, Ord)

-- Elaborated program
data Progs = Progs [Prog] (Term None) -- definitions, main
  deriving (Eq, Ord)

-- Constructor
data Ctor dparams = Ctor Var [Type dparams] -- ctor name, param types
deriving instance Eq (Ctor [])
deriving instance Eq (Ctor None)
deriving instance Ord (Ctor [])
deriving instance Ord (Ctor None)

instance HFunctor Ctor where
  hmap f (Ctor x as) = Ctor x (map (hmap f) as)

-- Variable
type Var = String

-- Param is (x : tp)
type Param dparams = (Var, Type dparams)
-- Arg is (tm : tp)
type Arg dparams = (Term dparams, Type dparams)

type IsTag = Bool

data Scheme = Forall [Var] [Var] (Type []) -- tags, type params, type
  deriving (Eq, Ord)

-- User-level term
data UsTm dparams =
    UsVar Var                               -- x
  | UsLam Var (Type dparams) (UsTm dparams) -- \ x : tp. tm
  | UsApp (UsTm dparams) (UsTm dparams)     -- tm1 tm2
  | UsCase (UsTm dparams) [CaseUs dparams]  -- case tm of case*
  | UsLet Var (UsTm dparams) (UsTm dparams) -- let x = tm1 in tm2
  | UsAmb [UsTm dparams]                    -- amb tm1 tm2 ... tmn
  | UsFactor Double (UsTm dparams)          -- factor wt in tm
  | UsFail (Type dparams)                   -- fail : tp
  | UsProd AddMult [UsTm dparams]           -- (tm1, ..., tmn)/<tm1, ..., tmn>
  | UsElimProd AddMult (UsTm dparams) [Var] (UsTm dparams)  -- let (x,y,z)/<x,y,z> = tm1 in tm2
  | UsTmBool Bool                           -- True / False
  | UsIf (UsTm dparams) (UsTm dparams) (UsTm dparams)       -- if tm1 then tm2 else tm3
  | UsEqs [UsTm dparams]                    -- tm1 == tm2 == ...
deriving instance Eq (UsTm [])
deriving instance Ord (UsTm [])

data GlobalVar = CtorVar | DefVar
  deriving (Eq, Ord)

-- Which kind of var: local function, global function, or constructor
data Scope = ScopeLocal | ScopeGlobal | ScopeCtor
  deriving (Eq, Show)

-- For the most part, the Type at the end of a constructor
-- below is the type of that expression as a whole
data Term dparams =
    TmVarL Var (Type dparams)                                                       -- Local var
  | TmVarG GlobalVar Var [Type dparams] [Arg dparams] (Type dparams)                -- Global var
  | TmLam Var (Type dparams) (Term dparams) (Type dparams)                          -- \ x : tp1. tm : tp2
  | TmApp (Term dparams) (Term dparams) (Type dparams) {- -> -} (Type dparams)      -- (tm1 : (tp1 -> tp2)) (tm2  : tp1) : tp2
  | TmLet Var (Term dparams) (Type dparams) (Term dparams) (Type dparams)           -- let x : tp1 = tm1 in tp2 : tp2
  | TmCase (Term dparams) (Var, [Type dparams]) [Case dparams] (Type dparams)       -- (case tm : y [tis] of case*) : tp
  | TmAmb [Term dparams] (Type dparams)                                             -- amb tm1 tm2 ... tmn : tp
  | TmFactor Double (Term dparams) (Type dparams)                                   -- factor wt in tm : tp
  | TmProd AddMult [Arg dparams]                                                    -- (tm1 : tp1, tm2 : tp2, ..., tmn : tpn) / <...>
  | TmElimProd AddMult (Term dparams) [Param dparams] (Term dparams) (Type dparams) -- let (x:X,y:Y,z:Z)/<...> = tm1 in tm2 : tp
  | TmEqs [Term dparams]                                                            -- tm1 == tm2 == ...
deriving instance Eq (Term [])
deriving instance Eq (Term None)
deriving instance Ord (Term [])
deriving instance Ord (Term None)

data AddMult = Additive | Multiplicative
  deriving (Eq, Ord)

data Type dparams =
    TpArr (Type dparams) (Type dparams) -- function
  | TpData Var (dparams (Type dparams)) -- datatype name with type arguments
  | TpVar Var                           -- type variable
  | TpProd AddMult [Type dparams]       -- additive or multiplicative product
  | NoTp                                -- nothing
deriving instance Eq (Type [])
deriving instance Eq (Type None)
deriving instance Ord (Type [])
deriving instance Ord (Type None)

instance HFunctor Type where
  hmap f (TpArr tp1 tp2) = TpArr (hmap f tp1) (hmap f tp2)
  hmap f (TpData y as)   = TpData y (f (fmap (hmap f) as))
  hmap f (TpVar y)       = TpVar y
  hmap f (TpProd am tps) = TpProd am (map (hmap f) tps)
  hmap f NoTp            = NoTp

toUsTp :: (HFunctor t, Functor dparams, Foldable dparams) => t dparams -> t []
toUsTp = hmap toList

data CaseUs dparams = CaseUs Var [Var] (UsTm dparams) -- | x a1 ... an -> tm
deriving instance Eq (CaseUs [])
deriving instance Ord (CaseUs [])

data Case dparams = Case Var [Param dparams] (Term dparams) -- | x (a1 : tp1) ... (an : tpn) -> tm
deriving instance Eq (Case [])
deriving instance Eq (Case None)
deriving instance Ord (Case [])
deriving instance Ord (Case None)
