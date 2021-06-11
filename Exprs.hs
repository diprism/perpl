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

data Ctor = Ctor Var [Type]

type Var = String

data Dist =
    DistFail
  | DistUni
  | DistAmb

data UsTm = -- User Term
    UsVar Var
  | UsLam Var Type UsTm
  | UsApp UsTm UsTm
  | UsCase UsTm [CaseUs]
  | UsSamp Dist Var
  deriving Show

data VarScope = ScopeLocal | ScopeGlobal | ScopeCtor

data Term =
    TmVar Var Type VarScope
  | TmLam Var Type Term Type
  | TmApp Term Term Type {- -> -} Type
  | TmCase Term [Case] Var Type
  | TmSamp Dist Var


data Type =
    TpArr Type Type
  | TpVar Var
--  | TpMeas Var
  deriving Eq

--type Arg = (Var, Type)
data CaseUs = CaseUs Var [Var] UsTm
  deriving Show

data Case = Case Var [(Var, Type)] Term



{- Show Instances -}

parensIf :: Bool -> String -> String
parensIf True s = "(" ++ s ++ ")"
parensIf False s = s

data ShowHist = ShowAppL | ShowAppR | ShowCase | ShowArrL | ShowTypeArg | ShowNone
  deriving Eq

-- Should we add parens to this term, given its parent term?
showTermParens :: Term -> ShowHist -> Bool
showTermParens (TmLam _ _ _ _)  ShowAppL = True
showTermParens (TmLam _ _ _ _)  ShowAppR = True
showTermParens (TmApp _ _ _ _)  ShowAppR = True
showTermParens (TmCase _ _ _ _) ShowAppL = True
showTermParens (TmCase _ _ _ _) ShowAppR = True
showTermParens (TmCase _ _ _ _) ShowCase = True
showTermParens (TmSamp _ _)     ShowAppL = True
showTermParens (TmSamp _ _)     ShowAppR = True
showTermParens _                _        = False

-- Should we add parens to this type, given its parent type?
showTypeParens :: Type -> ShowHist -> Bool
showTypeParens (TpArr _ _) ShowArrL = True
showTypeParens (TpArr _ _) ShowTypeArg = True
showTypeParens _ _ = False

-- Term show helper (ignoring parentheses)
showTermh :: Term -> String
showTermh (TmVar x _ _) = x
showTermh (TmLam x tp tm _) = "\\ " ++ x ++ " : " ++ show tp ++ ". " ++ showTerm tm ShowNone
showTermh (TmApp tm1 tm2 _ _) = showTerm tm1 ShowAppL ++ " " ++ showTerm tm2 ShowAppR
showTermh (TmCase tm cs _ _) = "case " ++ showTerm tm ShowCase ++ " of " ++ showCasesCtors cs
showTermh (TmSamp d y) = "sample " ++ show d ++ " " ++ y

-- Type show helper (ignoring parentheses)
showTypeh :: Type -> String
showTypeh (TpVar y) = y
showTypeh (TpArr tp1 tp2) = showType tp1 ShowArrL ++ " -> " ++ showType tp2 ShowNone

-- Show a term, given its parent for parentheses
showTerm :: Term -> ShowHist -> String
showTerm tm h = parensIf (showTermParens tm h) (showTermh tm)

-- Show a type, given its parent for parentheses
showType :: Type -> ShowHist -> String
showType tp h = parensIf (showTypeParens tp h) (showTypeh tp)

-- Generic case/ctor show function
--showCases :: [Case v Ctor] -> String
showCasesCtors [] = ""
showCasesCtors (c : []) = show c
showCasesCtors (c : cs) = show c ++ " | " ++ showCasesCtors cs

-- Actual show instances
instance Show Dist where
  show DistFail = "fail"
  show DistAmb = "amb"
  show DistUni = "uniform"

instance Show Case where
  show (Case x as tm) = foldl (\ x (a, tp) -> x ++ " " ++ a) x as ++ " -> " ++ show tm

instance Show Ctor where
  show (Ctor x as) = foldl (\ x a -> x ++ " " ++ showType a ShowTypeArg) x as

instance Show Term where
  show = flip showTerm ShowNone

instance Show Type where
  show = flip showType ShowNone

instance Show Progs where
  show (ProgExec tm) = "exec " ++ show tm
  show (ProgFun x tp tm ps) = "fun " ++ x ++ " : " ++ show tp ++ " = " ++ show tm ++ "\n\n" ++ show ps
  show (ProgData y cs ps) = "data " ++ y ++ " = " ++ showCasesCtors cs ++ "\n\n" ++ show ps
