module Show where
import Exprs
import Util

{- Convert back from elaborated terms to user terms -}

toUsTm :: Term -> UsTm
toUsTm (TmVarL x _) = UsVar x
toUsTm (TmVarG gv x as tp) =
  foldl (\ tm (a, _) -> UsApp tm (toUsTm a)) (UsVar x) as
toUsTm (TmLam x tp tm _) = UsLam x tp (toUsTm tm)
toUsTm (TmApp tm1 tm2 _ _) = UsApp (toUsTm tm1) (toUsTm tm2)
toUsTm (TmLet x xtm xtp tm tp) = UsLet x (toUsTm xtm) (toUsTm tm)
toUsTm (TmCase tm _ cs _) = UsCase (toUsTm tm) (map toCaseUs cs)
toUsTm (TmSamp d tp) = UsSamp d tp
-- TODO: better pretty printing of this
toUsTm (TmAmb tms tp) = UsAmb (map toUsTm tms)

toCaseUs :: Case -> CaseUs
toCaseUs (Case x as tm) = CaseUs x (map fst as) (toUsTm tm)

toUsProgs' :: [Prog] -> UsTm -> UsProgs
toUsProgs' (ProgFun x ps tm tp : ds) end = UsProgFun x (joinArrows (map snd ps) tp) (toUsTm (joinLams ps tm)) (toUsProgs' ds end)
toUsProgs' (ProgExtern x xp ps tp : ds) end = UsProgExtern x (joinArrows ps tp) (toUsProgs' ds end)
toUsProgs' (ProgData y cs : ds) end = UsProgData y cs (toUsProgs' ds end)
toUsProgs' [] end = UsProgExec end

toUsProgs :: Progs -> UsProgs
toUsProgs (Progs ps tm) = toUsProgs' ps (toUsTm tm)


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
showTermParens (UsAmb _    ) ShowAppL = True
showTermParens (UsAmb _    ) ShowAppR = True
showTermParens _             _        = False

-- Should we add parens to this type, given its parent type?
showTypeParens :: Type -> ShowHist -> Bool
showTypeParens (TpArr _ _) ShowArrL = True
showTypeParens (TpArr _ _) ShowTypeArg = True
showTypeParens _ _ = False

-- Term show helper (ignoring parentheses)
showTermh :: UsTm -> String
showTermh (UsVar x) = x
showTermh (UsLam x tp tm) = "\\ " ++ x ++ " : " ++ show tp ++ ". " ++ showTerm tm ShowNone
showTermh (UsApp tm1 tm2) = showTerm tm1 ShowAppL ++ " " ++ showTerm tm2 ShowAppR
showTermh (UsCase tm cs) = "case " ++ showTerm tm ShowCase ++ " of " ++ showCasesCtors cs
showTermh (UsSamp d tp) = "sample " ++ show d ++ " : " ++ show tp
showTermh (UsLet x tm tm') = "let " ++ x ++ " = " ++ showTerm tm ShowNone ++ " in " ++ showTerm tm' ShowNone
showTermh (UsAmb tms) = foldr (\ tm s -> s ++ " " ++ showTerm tm ShowAppR) "amb" tms

-- Type show helper (ignoring parentheses)
showTypeh :: Type -> String
showTypeh (TpVar y) = y
showTypeh (TpArr tp1 tp2) = showType tp1 ShowArrL ++ " -> " ++ showType tp2 ShowNone

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
