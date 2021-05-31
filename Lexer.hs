module Lexer where
import Exprs

data Token =
    TkVar Var
  | TkLam
--  | TkLamAff
--  | TkLamLin
  | TkParenL
  | TkParenR
--  | TkLet
--  | TkIn
  | TkEq
  | TkSample
  | TkObserve
  | TkFail
  | TkAmb
  | TkUni
  | TkMeas
--  | TkTrue
--  | TkFalse
--  | TkIf
--  | TkThen
--  | TkElse
--  | TkInl
--  | TkInr
  | TkCase
  | TkOf
--  | TkUnit
--  | TkBool
  | TkArr
--  | TkArrAff
--  | TkArrLin
  | TkLeftArr
--  | TkPlus
  | TkColon
  | TkDot
  | TkComma
  | TkBar
  | TkFun
  | TkData
  | TkExec
  deriving (Eq, Show)


--lexStrh :: String -> [Token] -> Maybe [Token]
lexStrh (' ' : s) = lexStrh s
lexStrh ('\n' : s) = lexStrh s
--lexStrh ('\\' : '?' : s) = lexAdd s TkLamAff
--lexStrh ('\\' : '1' : s) = lexAdd s TkLamLin
lexStrh ('\\' : s) = lexAdd s TkLam
--lexStrh ('-' : '>' : '?' : s) = lexAdd s TkArrAff
--lexStrh ('-' : '>' : '1' : s) = lexAdd s TkArrLin
lexStrh ('-' : '>' : s) = lexAdd s TkArr
lexStrh ('<' : '-' : s) = lexAdd s TkLeftArr
--lexStrh ('+' : s) = lexAdd s TkPlus
lexStrh (':' : s) = lexAdd s TkColon
lexStrh ('.' : s) = lexAdd s TkDot
lexStrh (',' : s) = lexAdd s TkComma
lexStrh ('|' : s) = lexAdd s TkBar
lexStrh ('=' : s) = lexAdd s TkEq
lexStrh ('(' : s) = lexAdd s TkParenL
lexStrh (')' : s) = lexAdd s TkParenR
lexStrh ('-' : '-' : s) = lexComment Nothing s
lexStrh ('{' : '-' : s) = lexComment (Just 0) s
lexStrh ('-' : '}' : s) = const Nothing
lexStrh "" = Just
lexStrh s = lexKeyword s

lexComment Nothing ('\n' : s) = lexStrh s
lexComment (Just 0) ('-' : '}' : s) = lexStrh s
lexComment (Just n) ('-' : '}' : s) = lexComment (Just (pred n)) s
lexComment (Just n) ('{' : '-' : s) = lexComment (Just (succ n)) s
lexComment multiline (_ : s) = lexComment multiline s
lexComment _ "" = Just

lexVar = h "" where
  h v (c : s) = if isVarChar c then h (c : v) s else Just (reverse v, (c : s))
  h v "" = Just (reverse v, "")

keywords = [
  ("fail", TkFail),
  ("amb", TkAmb),
  ("uniform", TkUni),
--  ("true", TkTrue),
--  ("false", TkFalse),
--  ("if", TkIf),
--  ("then", TkThen),
--  ("else", TkElse),
--  ("inl", TkInl),
--  ("inr", TkInr),
  ("case", TkCase),
  ("of", TkOf),
  ("measure", TkMeas),
  ("uniform", TkUni),
--  ("unit", TkUnit),
--  ("bool", TkBool),
--  ("let", TkLet),
--  ("in", TkIn),
  ("sample", TkSample),
  ("observe", TkObserve),
  ("fun", TkFun),
  ("data", TkData),
  ("exec", TkExec)]

lexKeyword s ts = lexVar s >>= \ (v, rest) -> if length v > 0 then trykw keywords v rest ts else Nothing where
  trykw ((kwstr, kwtok) : kws) v s = if kwstr == v then lexAdd s kwtok else trykw kws v s
  trykw [] v s = lexAdd s (TkVar v)


--varChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['\'', '_']
isVarChar c =
  (c >= 'a' && c <= 'z') ||
  (c >= 'A' && c <= 'Z') ||
  (c >= '0' && c <= '9') ||
  (c == '\'') ||
  (c == '_')


addTk f s t ts = f s (t : ts)
lexAdd = addTk lexStrh

lexStr = fmap reverse . flip lexStrh []
