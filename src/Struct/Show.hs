module Struct.Show where
import Data.List (intercalate)
import Util.Helpers
import Struct.Exprs
import Struct.Helpers

{- Convert back from elaborated terms to user terms -}

toUsTm :: Term -> UsTm
toUsTm (TmVarL x _) = UsVar x
toUsTm (TmVarG gv x tgs tis as _tp) =
  let x' = TmV (intercalate " " (show x : ["[" ++ p ++ "]" | p <- (show <$> tgs) ++ (show <$> tis)])) in
  foldl (\ tm (a, _) -> UsApp tm (toUsTm a)) (UsVar x') as
toUsTm (TmLam x tp tm _) = UsLam x tp (toUsTm tm)
toUsTm (TmApp tm1 tm2 _ _) = UsApp (toUsTm tm1) (toUsTm tm2)
toUsTm (TmLet x xtm xtp tm tp) = UsLet x (toUsTm xtm) (toUsTm tm)
toUsTm (TmCase tm (TpN "Bool", [], []) [Case (TmN "False") [] elsetm, Case (TmN "True") [] thentm] tp) = UsIf (toUsTm tm) (toUsTm thentm) (toUsTm elsetm)
toUsTm (TmCase tm _ cs _) = UsCase (toUsTm tm) (map toCaseUs cs)
toUsTm (TmAmb [] tp) = UsFail tp
toUsTm (TmAmb tms tp) = UsAmb [toUsTm tm | tm <- tms]
toUsTm (TmFactorDouble wt tm tp) = UsFactorDouble wt (toUsTm tm)
toUsTm (TmFactorNat wt tm tp) = UsFactorNat wt (toUsTm tm)
toUsTm (TmFactorRatio wt tm tp) = UsFactorRatio wt (toUsTm tm)
toUsTm (TmProd am as) = UsProd am [toUsTm tm | (tm, _) <- as]
toUsTm (TmElimMultiplicative tm ps    tm' tp) = UsElimMultiplicative (toUsTm tm) (fsts ps)   (toUsTm tm')
toUsTm (TmElimAdditive       tm n i p tm' tp) = UsElimAdditive       (toUsTm tm) n i (fst p) (toUsTm tm')
toUsTm (TmEqs tms) = UsEqs [toUsTm tm | tm <- tms]

toCaseUs :: Case -> CaseUs
toCaseUs (Case x as tm) = CaseUs x (fsts as) (toUsTm tm)

toUsProg :: Prog -> UsProg
toUsProg (ProgDefine x ps tm tp) = UsProgDefine x (toUsTm (joinLams ps tm)) (joinArrows (snds ps) tp)
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

showsPrecElim :: Int -> AddMult -> UsTm -> [ShowS] -> UsTm -> ShowS
showsPrecElim p am tm xs tm' = showParen (p > 1)
                             $ showString "let "
                             . showString l
                             . delimitWith ", " xs
                             . showString r
                             . showString " = "
                             . shows tm
                             . showString " in "
                             . showsPrec (if p == 1 then 1 else 0) tm'
  where (l, r) = amParens am

instance Show CaseUs where
  showsPrec p (CaseUs x as tm) = delimitWith " " (shows x : map shows as) . showString " -> " . showsPrec p tm
instance Show Case where
  showsPrec p = showsPrec p . toCaseUs

instance Show Ctor where
  showsPrec p (Ctor x as) = showParen (p > 10) (delimitWith " " (shows x : map (showsPrec 11) as))

instance Show UsTm where
  showsPrec _ (UsVar x) = shows x
  showsPrec p (UsApp tm1 tm2) = showParen (p > 10) (showsPrec 10 tm1 . showChar ' ' . showsPrec 11 tm2)
  showsPrec p (UsLam x tp tm) = showParen (p > 1) (showString "\\ " . shows x . showString (showTpAnn tp) . showString ". " . showsPrec (if p == 1 then 1 else 0) tm)
  showsPrec p (UsLet x tm tm') = showParen (p > 1) (showString "let " . shows x . showString " = " . shows tm . showString " in " . showsPrec (if p == 1 then 1 else 0) tm')
  showsPrec p (UsElimMultiplicative tm xs    tm') = showsPrecElim p Multiplicative tm (map shows xs) tm'
  showsPrec p (UsElimAdditive       tm n i x tm') = showsPrecElim p Additive tm [ if i==j then shows x else showString "_" | j <- [0..n-1] ] tm'
  showsPrec p (UsFactorDouble wt tm) = showParen (p > 1) (showString "factor " . shows wt . showString " in " . showsPrec (if p == 1 then 1 else 0) tm)
  showsPrec p (UsFactorNat wt tm) = showParen (p > 1) (showString "factor " . shows wt . showString " in " . showsPrec (if p == 1 then 1 else 0) tm)
  showsPrec p (UsFactorRatio wt tm) = showParen (p > 1) (showString "factor " . shows wt . showString " in " . showsPrec (if p == 1 then 1 else 0) tm)
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
  showsPrec _ (TpVar y) = shows y
  showsPrec _ (TpData y [] []) = shows y
  showsPrec p (TpData y tgs as) = showParen (p > 10) (delimitWith " " (shows y : map (showsPrec 11) tgs ++ map (showsPrec 11) as))
  showsPrec p (TpArr tp1 tp2) = showParen (p > 0) (showsPrec 1 tp1 . showString " -> " . shows tp2)
  showsPrec _ (TpProd am tps) = let (l, r) = amParens am in showString l . delimitWith ", " (map shows tps) . showString r
  showsPrec _ NoTp = id

instance Show UsProg where
  show (UsProgDefine x tm tp) = "define " ++ show x ++ showTpAnn tp ++ " = " ++ show tm ++ ";"
  show (UsProgExtern x tp) = "extern " ++ show x ++ showTpAnn tp ++ ";"
  show (UsProgData y ps []) = "data " ++ intercalate " " (show y : map show ps) ++ ";"
  show (UsProgData y ps cs) = "data " ++ intercalate " " (show y : map show ps) ++ " = " ++ intercalate " | " (map show cs) ++ ";"

instance Show UsProgs where
  show (UsProgs ps end) = intercalate "\n\n" ([show p | p <- ps] ++ [show end]) ++ "\n"

instance Show Forall where
  show (Forall x bd) =
    "∀" ++ (case bd of {BoundRobust -> "+"; BoundNone -> ""}) ++ " " ++ show x ++ "."

instance Show SProg where
  show (SProgDefine x tgs ps tm tp) = "define " ++ show x ++ " : " ++ intercalate " " (["∀ " ++ a ++ "." | a <- map show tgs] ++ map show ps ++ [show tp]) ++ " = " ++ show tm ++ ";"
  show (SProgExtern x tp) = "extern " ++ show x ++ " : " ++ show tp ++ ";"
  show (SProgData y tgs ps []) = "data " ++ intercalate " " (show y : map show tgs ++ map show ps) ++ ";"
  show (SProgData y tgs ps cs) = "data " ++ intercalate " " (show y : map show tgs ++ map show ps) ++ " = " ++ intercalate " | " [show c | c <- cs] ++ ";"

instance Show SProgs where
  show (SProgs ps end) = intercalate "\n\n" ([show p | p <- ps] ++ [show end]) ++ "\n"

instance Show Prog where
  show = show . toUsProg

instance Show Progs where
  show = show . toUsProgs

instance Show TmVar  where show (TmV x) = x
instance Show TmName where show (TmN x) = x
instance Show TpVar  where show (TpV x) = x
instance Show TpName where show (TpN x) = x
instance Show Tag    where show (Tag x) = x
