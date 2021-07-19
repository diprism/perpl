module Exprs where

data UsProgs =
    UsProgExec UsTm
  | UsProgFun String Type UsTm UsProgs
  | UsProgExtern String Type UsProgs
  | UsProgData String [Ctor] UsProgs

data Progs =
    ProgExec Term
  | ProgFun String Type Term Progs
  | ProgExtern String String Type Progs
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
  | UsSamp Dist Type
  | UsLet Var UsTm UsTm

data VarScope = ScopeLocal | ScopeGlobal | ScopeCtor
  deriving Eq

data Term =
    TmVar Var Type VarScope
  | TmLam Var Type Term Type
  | TmApp Term Term Type {- -> -} Type
  | TmCase Term Type [Case] Type
  | TmSamp Dist Type
  | TmCtor Var [(Term, Type)] Type
  -- For internal use only
--  | TmMaybe (Maybe Term) Type
--  | TmElimMaybe Term Type Term (Var, Term) Type
--  | TmBool Bool
--  | TmIf Term Term Term Type


data Type =
    TpArr Type Type
  | TpVar Var
  -- For internal use only
  | TpMaybe Type
  | TpBool
--  | TpMeas Var
  deriving Eq

data CaseUs = CaseUs Var [Var] UsTm

data Case = Case Var [(Var, Type)] Term

tpMaybeName   = "%Maybe%"
tpBoolName    = "%Bool%"
tmNothingName = "%nothing%"
tmJustName    = "%just%"
tmTrueName    = "%true%"
tmFalseName   = "%false%"

tmMaybe :: Maybe Term -> Type -> Term
tmMaybe Nothing tp = TmCtor tmNothingName [] (TpMaybe tp)
tmMaybe (Just tm) tp = TmCtor tmJustName [(tm, tp)] (TpMaybe tp)
tmElimMaybe :: Term -> Type -> Term -> (Var, Term) -> Type -> Term
tmElimMaybe tm tp ntm (jx, jtm) tp' =
  TmCase tm (TpMaybe tp) [Case tmNothingName [] ntm, Case tmJustName [(jx, tp)] jtm] tp'
tmBool :: Bool -> Term
tmBool b = TmCtor (if b then tmTrueName else tmFalseName) [] TpBool
tmIf :: Term -> Term -> Term -> Type -> Term
tmIf iftm thentm elsetm tp =
  TmCase iftm TpBool [Case tmFalseName [] elsetm, Case tmTrueName [] thentm] tp

boolCtors = [Ctor tmFalseName [], Ctor tmTrueName []]
maybeCtors tp = [Ctor tmNothingName [], Ctor tmJustName [tp]]

addTypeInst :: Var -> [Type] -> UsTm
addTypeInst x [] = UsVar x
addTypeInst x (tp : tps) = UsApp (UsVar x) (UsVar ("[" ++ foldl (\ s tp' -> s ++ ", " ++ show tp') (show tp) tps ++ "]"))

getTypeInst :: Type -> [Type]
getTypeInst (TpMaybe tp) = [tp]
getTypeInst _ = []

varTypeInst :: Var -> Type -> UsTm
varTypeInst x = addTypeInst x . getTypeInst

{- Convert back from elaborated terms to user terms -}

toUsTm :: Term -> UsTm
toUsTm (TmVar x _ _) = UsVar x
toUsTm (TmLam x tp tm _) = UsLam x tp (toUsTm tm)
toUsTm (TmApp tm1 tm2 _ _) = UsApp (toUsTm tm1) (toUsTm tm2)
toUsTm (TmCase tm _ cs _) = UsCase (toUsTm tm) (map toCaseUs cs)
toUsTm (TmSamp d tp) = UsSamp d tp
toUsTm (TmCtor x as tp) = foldl (\ tm (a, _) -> UsApp tm (toUsTm a)) (varTypeInst x tp) as

toCaseUs :: Case -> CaseUs
toCaseUs (Case x as tm) = CaseUs x (map fst as) (toUsTm tm)

toUsProgs :: Progs -> UsProgs
toUsProgs (ProgExec tm) = UsProgExec (toUsTm tm)
toUsProgs (ProgFun x tp tm ps) = UsProgFun x tp (toUsTm tm) (toUsProgs ps)
toUsProgs (ProgExtern x xp tp ps) = UsProgExtern x tp (toUsProgs ps)
toUsProgs (ProgData y cs ps) = UsProgData y cs (toUsProgs ps)


{- Show Instances -}

parens :: String -> String
parens s = "(" ++ s ++ ")"

parensIf :: Bool -> String -> String
parensIf True = parens
parensIf False = id

data ShowHist = ShowAppL | ShowAppR | ShowCase | ShowArrL | ShowTypeArg | ShowNone
  deriving Eq

-- Should we add parens to this term, given its parent term?
showTermParens :: UsTm -> ShowHist -> Bool
showTermParens (UsLam _ _ _) ShowAppL = True
showTermParens (UsLam _ _ _) ShowAppR = True
showTermParens (UsApp _ _  ) ShowAppR = True
showTermParens (UsCase _ _ ) ShowAppL = True
showTermParens (UsCase _ _ ) ShowAppR = True
showTermParens (UsCase _ _ ) ShowCase = True
showTermParens (UsSamp _ _ ) ShowAppL = True
showTermParens (UsSamp _ _ ) ShowAppR = True
showTermParens (UsLet _ _ _) ShowAppL = True
showTermParens (UsLet _ _ _) ShowAppR = True
showTermParens _             _        = False

-- Should we add parens to this type, given its parent type?
showTypeParens :: Type -> ShowHist -> Bool
showTypeParens (TpArr _ _) ShowArrL = True
showTypeParens (TpArr _ _) ShowTypeArg = True
showTypeParens (TpMaybe _) ShowTypeArg = True
showTypeParens _ _ = False

-- Term show helper (ignoring parentheses)
showTermh :: UsTm -> String
showTermh (UsVar x) = x
showTermh (UsLam x tp tm) = "\\ " ++ x ++ " : " ++ show tp ++ ". " ++ showTerm tm ShowNone
showTermh (UsApp tm1 tm2) = showTerm tm1 ShowAppL ++ " " ++ showTerm tm2 ShowAppR
showTermh (UsCase tm cs) = "case " ++ showTerm tm ShowNone ++ " of " ++ showCasesCtors cs
showTermh (UsSamp d tp) = "sample " ++ show d ++ " : " ++ show tp
showTermh (UsLet x tm tm') = "let " ++ x ++ " = " ++ showTerm tm ShowNone ++ " in " ++ showTerm tm' ShowNone

-- Type show helper (ignoring parentheses)
showTypeh :: Type -> String
showTypeh (TpVar y) = y
showTypeh (TpArr tp1 tp2) = showType tp1 ShowArrL ++ " -> " ++ showType tp2 ShowNone
showTypeh (TpMaybe tp) = tpMaybeName ++ " [" ++ showType tp ShowNone ++ "]"
showTypeh TpBool = tpBoolName

-- Show a term, given its parent for parentheses
showTerm :: UsTm -> ShowHist -> String
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

instance Show CaseUs where
  show (CaseUs x as tm) = foldl (\ x a -> x ++ " " ++ a) x as ++ " -> " ++ showTerm tm ShowCase
instance Show Case where
  show = show . toCaseUs

instance Show Ctor where
  show (Ctor x as) = foldl (\ x a -> x ++ " " ++ showType a ShowTypeArg) x as

instance Show UsTm where
  show = flip showTerm ShowNone
instance Show Term where
  show = show . toUsTm

instance Show Type where
  show = flip showType ShowNone

instance Show UsProgs where
  show (UsProgExec tm) = show tm
  show (UsProgFun x tp tm ps) = "define " ++ x ++ " : " ++ show tp ++ " = " ++ show tm ++ ";\n\n" ++ show ps
  show (UsProgExtern x tp ps) = "extern " ++ x ++ " : " ++ show tp ++ ";\n\n" ++ show ps
  show (UsProgData y cs ps) = "data " ++ y ++ " = " ++ showCasesCtors cs ++ ";\n\n" ++ show ps
instance Show Progs where
  show = show . toUsProgs
