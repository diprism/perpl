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

--data FnQual = FnUnr | FnAff | FnLin
--  deriving Show

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

data Term =
    TmVar Var Type
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

data ShowTermHist = ShowTermAppL | ShowTermAppR | ShowTermCase | ShowTermNone
  deriving Eq

data ShowTypeHist = ShowTypeArrL | ShowTypeArg | ShowTypeNone

showTermParens :: Term -> ShowTermHist -> Bool
showTermParens (TmLam _ _ _ _) ShowTermAppL = True
showTermParens (TmLam _ _ _ _) ShowTermAppR = True
showTermParens (TmApp _ _ _ _) ShowTermAppR = True
showTermParens (TmCase _ _ _ _) ShowTermAppL = True
showTermParens (TmCase _ _ _ _) ShowTermAppR = True
showTermParens (TmCase _ _ _ _) ShowTermCase = True
showTermParens (TmSamp _ _) ShowTermAppL = True
showTermParens (TmSamp _ _) ShowTermAppR = True
showTermParens _ _ = False

showTypeParens :: Type -> ShowTypeHist -> Bool
showTypeParens (TpArr _ _) ShowTypeArrL = True
showTypeParens (TpArr _ _) ShowTypeArg = True
showTypeParens _ _ = False

showTermh :: Term -> String
showTermh (TmVar x _) = x
showTermh (TmLam x tp tm _) = "\\ " ++ x ++ " : " ++ show tp ++ ". " ++ showTerm tm ShowTermNone
showTermh (TmApp tm1 tm2 _ _) = showTerm tm1 ShowTermAppL ++ " " ++ showTerm tm2 ShowTermAppR
showTermh (TmCase tm cs _ _) = "case " ++ showTerm tm ShowTermCase ++ " of " ++ showCasesCtors cs
showTermh (TmSamp d y) = "sample " ++ show d ++ " " ++ y

showTypeh :: Type -> String
showTypeh (TpVar y) = y
showTypeh (TpArr tp1 tp2) = showType tp1 ShowTypeArrL ++ " -> " ++ showType tp2 ShowTypeNone

showTerm :: Term -> ShowTermHist -> String
showTerm tm h = parensIf (showTermParens tm h) (showTermh tm)

showType :: Type -> ShowTypeHist -> String
showType tp h = parensIf (showTypeParens tp h) (showTypeh tp)

--showCases :: [Case v Ctor] -> String
showCasesCtors [] = ""
showCasesCtors (c : []) = show c
showCasesCtors (c : cs) = show c ++ " | " ++ showCasesCtors cs


instance Show Dist where
  show DistFail = "fail"
  show DistAmb = "amb"
  show DistUni = "uniform"

instance Show Case where
  show (Case x as tm) = foldl (\ x (a, tp) -> x ++ " " ++ a) x as ++ " -> " ++ show tm

instance Show Ctor where
  show (Ctor x as) = foldl (\ x a -> x ++ " " ++ showType a ShowTypeArg) x as

instance Show Term where
  show = flip showTerm ShowTermNone

instance Show Type where
  show = flip showType ShowTypeNone

instance Show Progs where
--      ProgExec Term
--  | ProgFun String Type Term Progs
--  | ProgData String [Ctor] Progs
  show (ProgExec tm) = "exec " ++ show tm
  show (ProgFun x tp tm ps) = "fun " ++ x ++ " : " ++ show tp ++ " = " ++ show tm ++ "\n\n" ++ show ps
  show (ProgData y cs ps) = "data " ++ y ++ " = " ++ showCasesCtors cs ++ "\n\n" ++ show ps
