module Struct.Show where
import Data.List (intercalate)
import Util.Helpers
import Struct.Exprs
import Struct.Helpers

{- Convert back from elaborated terms to user terms -}

toUsTm :: Term -> UsTm
toUsTm (TmVarL x _) = UsVar x
toUsTm (TmVarG gv x tis as tp) =
  foldl (\ tm (a, _) -> UsApp tm (toUsTm a)) (UsVar {- x -} (foldl (\ x tp -> x ++ " [" ++ show tp ++ "]") x tis)) as
toUsTm (TmLam x tp tm _) = UsLam x tp (toUsTm tm)
toUsTm (TmApp tm1 tm2 _ _) = UsApp (toUsTm tm1) (toUsTm tm2)
toUsTm (TmLet x xtm xtp tm tp) = UsLet x (toUsTm xtm) (toUsTm tm)
--toUsTm (TmCase tm "Bool" [Case "True" [] thentm, Case "False" [] elsetm] tp) = UsIf (toUsTm tm) (toUsTm thentm) (toUsTm elsetm)
toUsTm (TmCase tm ("Bool", []) [Case "False" [] elsetm, Case "True" [] thentm] tp) = UsIf (toUsTm tm) (toUsTm thentm) (toUsTm elsetm)
toUsTm (TmCase tm _ cs _) = UsCase (toUsTm tm) (map toCaseUs cs)
toUsTm (TmAmb [] tp) = UsFail tp
toUsTm (TmAmb tms tp) = UsAmb [toUsTm tm | tm <- tms]
toUsTm (TmFactor wt tm tp) = UsFactor wt (toUsTm tm)
toUsTm (TmProd am as) = UsProd am [toUsTm tm | (tm, _) <- as]
toUsTm (TmElimProd am tm ps tm' tp) = UsElimProd am (toUsTm tm) [x | (x, _) <- ps] (toUsTm tm')
toUsTm (TmEqs tms) = UsEqs [toUsTm tm | tm <- tms]

toCaseUs :: Case -> CaseUs
toCaseUs (Case x as tm) = CaseUs x (fsts as) (toUsTm tm)

toUsProg :: Prog -> UsProg
toUsProg (ProgFun x ps tm tp) = UsProgFun x (joinArrows (snds ps) tp) (toUsTm (joinLams ps tm))
toUsProg (ProgExtern x ps tp) = UsProgExtern x (joinArrows ps tp)
toUsProg (ProgData y cs) = UsProgData y [] cs

toUsProgs :: Progs -> UsProgs
--toUsProgs (Progs (ProgData "_Unit_" [unit] : ProgData "Bool" [fctor, tctor] : ps) tm) = UsProgs (map toUsProg ps) (toUsTm tm)
toUsProgs (Progs ps tm) = UsProgs (map toUsProg ps) (toUsTm tm)


{- Show Instances -}

data ShowHist = ShowAppL | ShowAppR | ShowEqs | ShowCase
              | ShowArrL | ShowTypeProd | ShowTypeArg
              | ShowNone
  deriving Eq

-- Should we add parens to this term, given its parent term?
showTermParens :: UsTm -> ShowHist -> Bool
showTermParens (UsLam _ _ _    ) ShowAppL = True
showTermParens (UsLam _ _ _    ) ShowAppR = True
showTermParens (UsLam _ _ _    ) ShowEqs  = True
showTermParens (UsApp _ _      ) ShowAppR = True
showTermParens (UsCase _ _     ) ShowAppL = True
showTermParens (UsCase _ _     ) ShowAppR = True
showTermParens (UsCase _ _     ) ShowCase = True
showTermParens (UsCase _ _     ) ShowEqs  = True
showTermParens (UsIf _ _ _     ) ShowAppL = True
showTermParens (UsIf _ _ _     ) ShowAppR = True
showTermParens (UsIf _ _ _     ) ShowEqs  = True
showTermParens (UsEqs _        ) ShowAppL = True
showTermParens (UsEqs _        ) ShowAppR = True
showTermParens (UsEqs _        ) ShowEqs  = True
showTermParens (UsLet _ _ _    ) ShowAppL = True
showTermParens (UsLet _ _ _    ) ShowAppR = True
showTermParens (UsLet _ _ _    ) ShowEqs  = True
showTermParens (UsAmb _        ) ShowAppL = True
showTermParens (UsAmb _        ) ShowAppR = True
showTermParens (UsFactor _ _   ) ShowAppL = True
showTermParens (UsFactor _ _   ) ShowAppR = True
showTermParens (UsFail NoTp    ) ShowAppL = False
showTermParens (UsFail _       ) ShowAppL = True
showTermParens (UsFail _       ) ShowAppR = True
showTermParens (UsFail _       ) ShowEqs  = True
showTermParens (UsElimProd _ _ _ _) ShowAppL = True
showTermParens (UsElimProd _ _ _ _) ShowAppR = True
showTermParens (UsElimProd _ _ _ _) ShowEqs  = True
showTermParens _                 _        = False

-- Should we add parens to this type, given its parent type?
showTypeParens :: Type -> ShowHist -> Bool
showTypeParens (TpArr _ _) ShowArrL = True
showTypeParens (TpArr _ _) ShowTypeProd = True
showTypeParens (TpArr _ _) ShowTypeArg = True
showTypeParens (TpProd _ (_ : _ : _)) ShowTypeProd = True
showTypeParens (TpProd _ (_ : _ : _)) ShowTypeArg = True
showTypeParens (TpVar _ (_ : _)) ShowTypeArg = True
showTypeParens _ _ = False

showTpAnn :: Type -> String
showTpAnn NoTp = ""
showTpAnn tp = " : " ++ show tp

amParens :: AddMult -> (String, String)
amParens Additive = ("<", ">")
amParens Multiplicative = ("(", ")")

-- Term show helper (ignoring parentheses)
showTermh :: UsTm -> String
showTermh (UsVar x) = x
showTermh (UsLam x tp tm) = "\\ " ++ x ++ showTpAnn tp ++ ". " ++ showTerm tm ShowNone
showTermh (UsApp tm1 tm2) = showTerm tm1 ShowAppL ++ " " ++ showTerm tm2 ShowAppR
showTermh (UsCase tm cs) = "case " ++ showTerm tm ShowNone ++ " of " ++ showCasesCtors cs
showTermh (UsIf tm1 tm2 tm3) = "if " ++ showTerm tm1 ShowNone ++ " then " ++ showTerm tm2 ShowNone ++ " else " ++ showTerm tm3 ShowNone
showTermh (UsTmBool b) = if b then "True" else "False"
showTermh (UsLet x tm tm') = "let " ++ x ++ " = " ++ showTerm tm ShowNone ++ " in " ++ showTerm tm' ShowNone
showTermh (UsAmb tms) = foldl (\ s tm -> s ++ " " ++ showTerm tm ShowAppR) "amb" tms
showTermh (UsFactor wt tm) = "factor " ++ show wt ++ " in " ++ showTerm tm ShowNone
showTermh (UsFail tp) = "fail" ++ showTpAnn tp
showTermh (UsProd am tms) =
  let (l, r) = amParens am in
    l ++ intercalate ", " [showTerm tm ShowNone | tm <- tms] ++ r
showTermh (UsElimProd am tm xs tm') =
  let (l, r) = amParens am in
    "let " ++ l ++ intercalate ", " xs ++ r ++ " = " ++ showTerm tm ShowNone ++ " in " ++ showTerm tm' ShowNone
showTermh (UsEqs tms) = intercalate " == " [showTerm tm ShowEqs | tm <- tms]

-- Type show helper (ignoring parentheses)
showTypeh :: Type -> String
showTypeh (TpVar y as) = intercalate " " (y : [showType a ShowTypeArg | a <- as])
showTypeh (TpArr tp1 tp2) = showType tp1 ShowArrL ++ " -> " ++ showType tp2 ShowNone
showTypeh (TpProd Multiplicative []) = "Unit"
showTypeh (TpProd Additive []) = "Top"
showTypeh (TpProd am tps) = intercalate (if am == Additive then " & " else " * ") [showType tp ShowTypeArg | tp <- tps]
showTypeh NoTp = ""

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

instance Show Scheme where
  show (Forall [] [] tp) = show tp
  show (Forall tgs tpms tp) = "Forall " ++ intercalate ", " (tgs ++ tpms) ++ ". " ++ show tp

instance Show UsProg where
  show (UsProgFun x tp tm) = "define " ++ x ++ showTpAnn tp ++ " = " ++ show tm ++ ";"
  show (UsProgExtern x tp) = "extern " ++ x ++ showTpAnn tp ++ ";"
  show (UsProgData y ps []) = "data " ++ intercalate " " (y : ps) ++ ";"
  show (UsProgData y ps cs) = "data " ++ intercalate " " (y : ps) ++ " = " ++ showCasesCtors cs ++ ";"
instance Show UsProgs where
  show (UsProgs ps end) = intercalate "\n\n" ([show p | p <- ps] ++ [show end]) ++ "\n"
instance Show Progs where
  show = show . toUsProgs
instance Show SProgs where
  show (SProgs ps end) = intercalate "\n\n" ([show p | p <- ps] ++ [show end]) ++ "\n"
instance Show SProg where
  show (SProgFun x stp tm) = "define " ++ x ++ " : " ++ show stp ++ " = " ++ show tm ++ ";"
  show (SProgExtern x tps tp) = "extern " ++ x ++ " : " ++ show (joinArrows tps tp) ++ ";"
  show (SProgData y tgs ps cs) = "data " ++ intercalate " " (y : tgs ++ ps) ++ " = " ++ intercalate " | " [show c | c <- cs] ++ ";"
