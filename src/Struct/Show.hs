module Struct.Show where
import Data.List (intercalate)
import Util.Helpers
import Struct.Exprs
import Struct.Helpers

{- Convert back from elaborated terms to user terms -}

toUsTm :: Term -> UsTm
toUsTm (TmVarL x _) = UsVar x
toUsTm (TmVarG gv x tgs tis as _tp) =
  let x' = intercalate " " (x : ["[" ++ p ++ "]" | p <- (show <$> tgs) ++ (show <$> tis)]) in
  foldl (\ tm (a, _) -> UsApp tm (toUsTm a)) (UsVar x') as
toUsTm (TmLam x tp tm _) = UsLam x tp (toUsTm tm)
toUsTm (TmApp tm1 tm2 _ _) = UsApp (toUsTm tm1) (toUsTm tm2)
toUsTm (TmLet x xtm xtp tm tp) = UsLet x (toUsTm xtm) (toUsTm tm)
--toUsTm (TmCase tm "Bool" [Case "True" [] thentm, Case "False" [] elsetm] tp) = UsIf (toUsTm tm) (toUsTm thentm) (toUsTm elsetm)
toUsTm (TmCase tm ("Bool", [], []) [Case "False" [] elsetm, Case "True" [] thentm] tp) = UsIf (toUsTm tm) (toUsTm thentm) (toUsTm elsetm)
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
toUsProg (ProgFun x ps tm tp) = UsProgFun x (toUsTm (joinLams ps tm)) (joinArrows (snds ps) tp)
toUsProg (ProgExtern x ps tp) = UsProgExtern x (joinArrows ps tp)
toUsProg (ProgData y cs) = UsProgData y [] cs

toUsProgs :: Progs -> UsProgs
--toUsProgs (Progs (ProgData "_Unit_" [unit] : ProgData "Bool" [fctor, tctor] : ps) tm) = UsProgs (map toUsProg ps) (toUsTm tm)
toUsProgs (Progs ps tm) = UsProgs (map toUsProg ps) (toUsTm tm)


{- Show Instances -}

showTpAnn :: Type -> String
showTpAnn NoTp = ""
showTpAnn tp = " : " ++ show tp

amParens :: AddMult -> (String, String)
amParens Additive = ("<", ">")
amParens Multiplicative = ("(", ")")

instance Show CaseUs where
  showsPrec p (CaseUs x as tm) = delimitWith " " (map showString (x:as)) . showString " -> " . showsPrec p tm
instance Show Case where
  showsPrec p = showsPrec p . toCaseUs

instance Show Ctor where
  showsPrec p (Ctor x as) = showParen (p > 10) (delimitWith " " (showString x : map (showsPrec 11) as))

instance Show UsTm where
  showsPrec _ (UsVar x) = showString x
  showsPrec p (UsApp tm1 tm2) = showParen (p > 10) (showsPrec 10 tm1 . showChar ' ' . showsPrec 11 tm2)
  showsPrec p (UsLam x tp tm) = showParen (p > 1) (showString "\\ " . showString x . showString (showTpAnn tp) . showString ". " . showsPrec (if p == 1 then 1 else 0) tm)
  showsPrec p (UsLet x tm tm') = showParen (p > 1) (showString "let " . showString x . showString " = " . shows tm . showString " in " . showsPrec (if p == 1 then 1 else 0) tm')
  showsPrec p (UsElimProd am tm xs tm') = showParen (p > 1) (let (l, r) = amParens am in showString "let " . showString l . delimitWith ", " (map showString xs) . showString r . showString " = " . shows tm . showString " in " . showsPrec (if p == 1 then 1 else 0) tm')
  showsPrec p (UsFactor wt tm) = showParen (p > 1) (showString "factor " . shows wt . showString " in " . showsPrec (if p == 1 then 1 else 0) tm)
  showsPrec p (UsIf tm1 tm2 tm3) = showParen (p > 1) (showString "if " . shows tm1 . showString " then " . shows tm2 . showString " else " . showsPrec (if p == 1 then 1 else 0) tm3)
  showsPrec p (UsCase tm cs) = showParen (p > 0) (showString "case " . shows tm . showString " of " . delimitWith " | " (map (showsPrec 1) cs))
  showsPrec p (UsAmb tms) = showParen (p > 9) (delimitWith " " (showString "amb" : map (showsPrec 11) tms))
  showsPrec p (UsFail tp) = showParen (tp /= NoTp && p > 1) (showString "fail" . showString (showTpAnn tp))
  showsPrec _ (UsProd am tms) = let (l, r) = amParens am in showString l . delimitWith ", " (map shows tms) . showString r
  showsPrec _ (UsTmBool b) = showString (if b then "True" else "False")
  showsPrec p (UsEqs tms) = showParen (p > 4) (delimitWith " == " (map (showsPrec 5) tms))
instance Show Term where
  showsPrec p = showsPrec p . toUsTm

instance Show Type where
  showsPrec _ (TpVar y) = showString y
  showsPrec _ (TpData y [] []) = showString y
  showsPrec p (TpData y tgs as) = showParen (p > 10) (delimitWith " " (showString y : map (showsPrec 11) tgs ++ map (showsPrec 11) as))
  showsPrec p (TpArr tp1 tp2) = showParen (p > 0) (showsPrec 1 tp1 . showString " -> " . shows tp2)
  showsPrec _ (TpProd am tps) = let (l, r) = amParens am in showString l . delimitWith ", " (map shows tps) . showString r
  showsPrec _ NoTp = id

instance Show UsProg where
  show (UsProgFun x tm tp) = "define " ++ x ++ showTpAnn tp ++ " = " ++ show tm ++ ";"
  show (UsProgExtern x tp) = "extern " ++ x ++ showTpAnn tp ++ ";"
  show (UsProgData y ps []) = "data " ++ intercalate " " (y : ps) ++ ";"
  show (UsProgData y ps cs) = "data " ++ intercalate " " (y : ps) ++ " = " ++ intercalate " | " (map show cs) ++ ";"

instance Show UsProgs where
  show (UsProgs ps end) = intercalate "\n\n" ([show p | p <- ps] ++ [show end]) ++ "\n"

instance Show SProg where
  show (SProgFun x tgs ps tm tp) = "define " ++ x ++ " : " ++ intercalate " " (["∀ "++a++"." | a <- tgs ++ ps] ++ [show tp]) ++ " = " ++ show tm ++ ";"
  show (SProgExtern x tp) = "extern " ++ x ++ " : " ++ show tp ++ ";"
  show (SProgData y tgs ps cs) = "data " ++ intercalate " " (y : tgs ++ ps) ++ " = " ++ intercalate " | " [show c | c <- cs] ++ ";"

instance Show SProgs where
  show (SProgs ps end) = intercalate "\n\n" ([show p | p <- ps] ++ [show end]) ++ "\n"

instance Show Prog where
  show = show . toUsProg

instance Show Progs where
  show = show . toUsProgs

instance Show Tag where
  show (TgVar tg) = tg
