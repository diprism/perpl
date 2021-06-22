module Lex where
import Exprs

-- Possible tokens
data Token =
    TkVar Var
  | TkLam
  | TkParenL
  | TkParenR
  | TkEq
  | TkSample
  | TkFail
  | TkAmb
  | TkUni
  | TkMeas
  | TkCase
  | TkOf
  | TkArr
  | TkLeftArr
  | TkColon
  | TkDot
  | TkComma
  | TkBar
  | TkFun
  | TkData
--  | TkExec
  | TkSemicolon
  deriving (Eq, Show)

-- Lex a string, returning a list of tokens
lexStrh :: String -> [Token] -> Maybe [Token]
lexStrh (' ' : s) = lexStrh s
lexStrh ('\n' : s) = lexStrh s
lexStrh ('\\' : s) = lexAdd s TkLam
lexStrh ('-' : '>' : s) = lexAdd s TkArr
lexStrh ('<' : '-' : s) = lexAdd s TkLeftArr
lexStrh (':' : s) = lexAdd s TkColon
lexStrh ('.' : s) = lexAdd s TkDot
lexStrh (',' : s) = lexAdd s TkComma
lexStrh (';' : s) = lexAdd s TkSemicolon
lexStrh ('|' : s) = lexAdd s TkBar
lexStrh ('=' : s) = lexAdd s TkEq
lexStrh ('(' : s) = lexAdd s TkParenL
lexStrh (')' : s) = lexAdd s TkParenR
lexStrh ('-' : '-' : s) = lexComment Nothing s
lexStrh ('{' : '-' : s) = lexComment (Just 0) s
lexStrh ('-' : '}' : s) = const Nothing
lexStrh "" = Just
lexStrh s = lexKeywordOrVar s

-- Lex a comment.
-- lexComment Nothing scans a comment from -- to the end of the line.
-- lexComment (Just n) scans a nested comment (inside {- and -}).
lexComment :: Maybe Integer -> String -> [Token] -> Maybe [Token]
lexComment Nothing ('\n' : s) = lexStrh s
lexComment (Just 0) ('-' : '}' : s) = lexStrh s
lexComment (Just n) ('-' : '}' : s) = lexComment (Just (pred n)) s
lexComment (Just n) ('{' : '-' : s) = lexComment (Just (succ n)) s
lexComment multiline (_ : s) = lexComment multiline s
lexComment _ "" = Just

-- Consumes characters until a non-variable character is reached
lexVar :: String -> Maybe (String, String)
lexVar = h "" where
  h v (c : s) = if isVarChar c then h (c : v) s else Just (reverse v, (c : s))
  h v "" = Just (reverse v, "")

-- Determines if c is a valid character for a variable name
--varChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['\'', '_']
isVarChar :: Char -> Bool
isVarChar c =
  (c >= 'a' && c <= 'z') ||
  (c >= 'A' && c <= 'Z') ||
  (c >= '0' && c <= '9') ||
  (c == '\'') ||
  (c == '_')

-- List of keywords and the names that lex as them
keywords = [
  ("fail", TkFail),
  ("amb", TkAmb),
  ("uniform", TkUni),
  ("case", TkCase),
  ("of", TkOf),
  ("measure", TkMeas),
  ("uniform", TkUni),
  ("sample", TkSample),
  ("define", TkFun),
--  ("exec", TkExec),
  ("data", TkData)]

-- Lex a keyword or a variable name.
lexKeywordOrVar :: String -> [Token] -> Maybe [Token]
lexKeywordOrVar s ts = lexVar s >>= \ (v, rest) -> if length v > 0 then trykw keywords v rest ts else Nothing where
  trykw ((kwstr, kwtok) : kws) v s = if kwstr == v then lexAdd s kwtok else trykw kws v s
  trykw [] v s = lexAdd s (TkVar v)

-- Add a token, and continue lexing
lexAdd :: String -> Token -> [Token] -> Maybe [Token]
lexAdd s t ts = lexStrh s (t : ts)

-- Lex a program.
lexStr :: String -> Maybe [Token]
lexStr = fmap reverse . flip lexStrh []
