module Parser where

data Progs = ProgNil Term | ProgCons String [Arg] Term Progs
  deriving Show

data FnQual = FnUnr | FnAff | FnLin
  deriving Show

type Var = String

data InjLR = Inl | Inr
  deriving Show

data Term =
    TmVar Var
  | TmLam FnQual Var Type Term
  | TmApp Term Term
  | TmLet Var Type Term Term
  | TmSamp Term
  | TmObs Term Term
  | TmFail
  | TmBool Bool
  | TmIf Term Term Term
  | TmInj InjLR
  | TmCase Term Var Term Var Term
  | TmUnit
  deriving Show

data Type =
    TpUnit
  | TpBool
  | TpArr Type FnQual Type
  | TpSum Type Type
  deriving Show

type Arg = Bool -- TODO


data Token =
    TkVar Var
  | TkLam
  | TkLamAff
  | TkLamLin
  | TkParenL
  | TkParenR
  | TkLet
  | TkIn
  | TkEq
  | TkSample
  | TkObserve
  | TkFail
  | TkTrue
  | TkFalse
  | TkIf
  | TkThen
  | TkElse
  | TkInl
  | TkInr
  | TkCase
  | TkOf
  | TkUnit
  | TkBool
  | TkArr
  | TkArrAff
  | TkArrLin
  | TkLeftArr
  | TkPlus
  | TkColon
  | TkDot
  | TkBar
  deriving (Eq, Show)


--lexStrh :: String -> [Token] -> Maybe [Token]
lexStrh (' ' : s) = lexStrh s
lexStrh ('\n' : s) = lexStrh s
lexStrh ('\\' : '?' : s) = lexAdd s TkLamAff
lexStrh ('\\' : '1' : s) = lexAdd s TkLamLin
lexStrh ('\\' : s) = lexAdd s TkLam
lexStrh ('-' : '?' : '>' : s) = lexAdd s TkArrAff
lexStrh ('-' : '1' : '>' : s) = lexAdd s TkArrLin
lexStrh ('-' : '>' : s) = lexAdd s TkArr
lexStrh ('<' : '-' : s) = lexAdd s TkLeftArr
lexStrh ('+' : s) = lexAdd s TkPlus
lexStrh (':' : s) = lexAdd s TkColon
lexStrh ('.' : s) = lexAdd s TkDot
lexStrh ('|' : s) = lexAdd s TkBar
lexStrh ('=' : s) = lexAdd s TkEq
lexStrh ('(' : s) = lexAdd s TkParenL
lexStrh (')' : s) = lexAdd s TkParenR
lexStrh "" = Just
lexStrh s = lexKeyword s

{-
lexVar = h "" where
  h v (c : s) = if isVarChar c then h s (c : v) else lexAdd s (TkVar (reverse v))
  h v "" = \ ts -> Just (TkVar (reverse v) : ts)
-}
lexVar = h "" where
  h v (c : s) = if isVarChar c then h (c : v) s else Just (reverse v, (c : s))
  h v "" = Just (reverse v, "")

keywords = [
  ("fail", TkFail),
  ("true", TkTrue),
  ("false", TkFalse),
  ("if", TkIf),
  ("then", TkThen),
  ("else", TkElse),
  ("inl", TkInl),
  ("inr", TkInr),
  ("case", TkCase),
  ("of", TkOf),
  ("unit", TkUnit),
  ("bool", TkBool),
  ("let", TkLet),
  ("in", TkIn),
  ("sample", TkSample),
  ("observe", TkObserve) ]

lexKeyword s ts = lexVar s >>= \ (v, rest) -> if length v > 0 then trykw keywords v rest ts else Nothing where
  trykw ((kwstr, kwtok) : kws) v s = if kwstr == v then lexAdd s kwtok else trykw kws v s
  trykw [] v s = lexAdd s (TkVar v)

{-
lexKeyword = h keywords where
  trykw (k : ks) (c : cs) = if k == c then trykw ks cs else Nothing
  trykw [] (c : cs) = if isVarChar c then Nothing else Just (c : cs)
  trykw [] [] = Just []
  
  h ((kwstr, kwtok) : kws) s =
    maybe (h kws s) (\ rest -> lexAdd rest kwtok) $ trykw kwstr s
  h [] s = lexVar s
-}


--varChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['\'', '_']
isVarChar c =
  (c >= 'a' && c <= 'z') ||
  (c >= 'A' && c <= 'Z') ||
  (c >= '0' && c <= '9') ||
  (c == '\'') ||
  (c == '_')


addTk f s t ts = f s (t : ts)
lexAdd = addTk lexStrh


newtype ParseM a = ParseM ([Token] -> Maybe (a, [Token]))

parseMf (ParseM f) = f
parseMt ts (ParseM f) = f ts
parseMr = curry Just

parseDrop t = ParseM $ \ ts -> case ts of
  (t' : ts') -> if t == t' then parseMr () ts' else Nothing
  _ -> Nothing

instance Functor ParseM where
  fmap f (ParseM g) = ParseM $ \ ts -> g ts >>= \ p -> Just (f (fst p), snd p)

instance Applicative ParseM where
  pure = ParseM . parseMr
  ParseM f <*> ParseM g =
    ParseM $ \ ts -> f ts >>= \ p ->
    g (snd p) >>= \ p' ->
    Just (fst p (fst p'), snd p')

instance Monad ParseM where
  (ParseM f) >>= g = ParseM $ \ ts -> f ts >>= \ (a, ts') -> parseMf (g a) ts'


parseVar = ParseM $ \ ts -> case ts of
  (TkVar v : ts) -> parseMr v ts
  _ -> Nothing

-- Lam, Let, Sample, Observe, If, Case
parseTerm1 = ParseM $ \ ts -> case ts of
  (TkLam : ts) -> parseMt ts $ pure (TmLam FnUnr) <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseTerm1
  (TkLamAff : ts) -> parseMt ts $ pure (TmLam FnAff) <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseTerm1
  (TkLamLin : ts) -> parseMt ts $ pure (TmLam FnLin) <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseTerm1
  (TkLet : ts) -> parseMt ts $ pure TmLet <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkEq <*> parseTerm1 <* parseDrop TkIn <*> parseTerm1
  (TkSample : ts) -> parseMt ts $ pure TmSamp <*> parseTerm1
  (TkObserve : ts) -> parseMt ts $ pure TmObs <*> parseTerm1 <* parseDrop TkLeftArr <*> parseTerm1
  (TkIf : ts) -> parseMt ts $ pure TmIf <*> parseTerm1 <* parseDrop TkThen <*> parseTerm1 <* parseDrop TkElse <*> parseTerm1
  (TkCase : ts) -> parseMt ts $ pure TmCase <*> parseTerm1 <* parseDrop TkOf <* parseDrop TkInl <*> parseVar <* parseDrop TkArr <*> parseTerm1 <* parseDrop TkBar <* parseDrop TkInr <*> parseVar <* parseDrop TkArr <*> parseTerm1
  _ -> parseMt ts parseTerm2

-- App
parseTerm2 = ParseM $ \ ts -> parseMt ts parseTerm3 >>= uncurry (parseMf . parseTermApp)

parseTermApp tm = ParseM $ \ ts ->
  maybe
    (parseMr tm ts)
    (uncurry $ parseMf . parseTermApp . TmApp tm)
    (parseMt ts parseTerm3)

-- Var, Fail, Unit, True, False, Inl, Inr, Parens
parseTerm3 = ParseM $ \ ts -> case ts of
  (TkVar v : ts) -> parseMr (TmVar v) ts
  (TkFail : ts) -> parseMr TmFail ts
  (TkUnit : ts) -> parseMr TmUnit ts
  (TkTrue : ts) -> parseMr (TmBool True) ts
  (TkFalse : ts) -> parseMr (TmBool False) ts
  (TkInl : ts) -> parseMr (TmInj Inl) ts
  (TkInr : ts) -> parseMr (TmInj Inr) ts
  (TkParenL : ts) -> parseMt ts $ parseTerm1 <* parseDrop TkParenR
  _ -> Nothing


--parseType1 :: ParseM Type
parseType1 = ParseM $ \ ts -> parseMt ts parseType2 >>= \ (tp, ts) -> case ts of
  (TkArr    : ts) -> parseMt ts $ pure (TpArr tp FnUnr) <*> parseType1
  (TkArrAff : ts) -> parseMt ts $ pure (TpArr tp FnAff) <*> parseType1
  (TkArrLin : ts) -> parseMt ts $ pure (TpArr tp FnLin) <*> parseType1
  _ -> parseMr tp ts

--parseType2 :: ParseM Type
parseType2 = ParseM $ \ ts -> parseMt ts parseType3 >>= \ (tp, ts') -> case ts' of
  (TkPlus : ts') -> parseMt ts' $ pure (TpSum tp) <*> parseType3
  _ -> parseMr tp ts'

--parseType3 :: ParseM Type
parseType3 = ParseM $ \ ts -> case ts of
  (TkUnit : ts) -> parseMr TpUnit ts
  (TkBool : ts) -> parseMr TpBool ts
  (TkParenL : ts) -> parseMt ts $ parseType1 <* parseDrop TkParenR
  _ -> Nothing


parseTerm ts = parseMf parseTerm1 ts >>= \ (tm, ts') -> if length ts' == 0 then Just tm else Nothing
parseType ts = parseMf parseType1 ts >>= \ (tp, ts') -> if length ts' == 0 then Just tp else Nothing
lexStr = fmap reverse . flip lexStrh []
