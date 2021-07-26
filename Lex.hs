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
  | TkCase
  | TkOf
  | TkLet
  | TkIn
  | TkArr
  | TkLeftArr
  | TkColon
  | TkDot
  | TkComma
  | TkBar
  | TkSemicolon
  | TkFun
  | TkExtern
  | TkData
  deriving Eq

instance Show Token where
  show (TkVar x) = x
  -- Punctuation tokens
  show TkLam = "\\"
  show TkParenL = "("
  show TkParenR = ")"
  show TkEq = "="
  show TkArr = "->"
  show TkLeftArr = "<-"
  show TkColon = ":"
  show TkDot = "."
  show TkComma = ","
  show TkBar = "|"
  show TkSemicolon = ";"
  -- Keyword tokens
  show TkSample = "sample"
  show TkFail = "fail"
  show TkAmb = "amb"
  show TkUni = "uniform"
  show TkCase = "case"
  show TkOf = "of"
  show TkLet = "let"
  show TkIn = "in"
  show TkFun = "define"
  show TkExtern  = "extern"
  show TkData = "data"


type Pos = (Int, Int) -- Line, column

forward' :: Int -> Pos -> Pos
forward' n (line, column) = (line, column + n)
forward = forward' 1

next :: Pos -> Pos
next (line, column) = (succ line, 0)

-- List of punctuation tokens
punctuation = [TkLam, TkParenL, TkParenR, TkEq, TkArr, TkLeftArr, TkColon, TkDot, TkComma, TkBar, TkSemicolon]
-- List of keyword tokens (use alphanumeric chars)
keywords = [TkFail, TkAmb, TkUni, TkCase, TkOf, TkLet, TkIn, TkUni, TkSample, TkFun, TkExtern, TkData]

lexPunctuation :: String -> Pos -> [(Pos, Token)] -> Either Pos [(Pos, Token)]
lexPunctuation s =
  foldr (\ t owise -> maybe owise (flip (lexAdd (show t)) t) (prefix (show t) s))
        (lexKeywordOrVar s)
        punctuation
  where
    prefix (tc : tcs) (c : cs) =
      if tc == c then prefix tcs cs else Nothing
    prefix [] s = Just s
    prefix _ [] = Nothing


-- Lex a string, returning a list of tokens
lexStrh :: String -> Pos -> [(Pos, Token)] -> Either Pos [(Pos, Token)]
lexStrh (' ' : s) = lexStrh s . forward
lexStrh ('\n' : s) = lexStrh s . next
lexStrh ('-' : '-' : s) = lexComment Nothing s
lexStrh ('{' : '-' : s) = lexComment (Just 0) s
lexStrh ('-' : '}' : s) = \ p _ -> Left p
lexStrh "" = \ _ ts -> Right ts
lexStrh s = lexPunctuation s

-- Lex a comment.
-- lexComment Nothing scans a comment from -- to the end of the line.
-- lexComment (Just n) scans a nested comment (inside {- and -}).
lexComment :: Maybe Integer -> String -> Pos -> [(Pos, Token)] -> Either Pos [(Pos, Token)]
lexComment Nothing  ('\n' : s) = lexStrh s . next
lexComment (Just n) ('\n' : s) = lexComment (Just n) s . next
lexComment (Just 0) ('-' : '}' : s) = lexStrh s . forward' 2
lexComment (Just n) ('-' : '}' : s) = lexComment (Just (pred n)) s . forward' 2
lexComment (Just n) ('{' : '-' : s) = lexComment (Just (succ n)) s . forward' 2
lexComment multiline (_ : s) = lexComment multiline s . forward
lexComment _ "" = \ _ ts -> Right ts

-- Consumes characters until a non-variable character is reached
lexVar :: String -> (String, String)
lexVar = h "" where
  h v (c : s) = if isVarChar c then h (c : v) s else (reverse v, (c : s))
  h v "" = (reverse v, "")

-- Determines if c is a valid character for a variable name
--varChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['\'', '_']
isVarChar :: Char -> Bool
isVarChar c =
  (c >= 'a' && c <= 'z') ||
  (c >= 'A' && c <= 'Z') ||
  (c >= '0' && c <= '9') ||
  (c == '\'') ||
  (c == '_')

-- Lex a keyword or a variable name
lexKeywordOrVar :: String -> Pos -> [(Pos, Token)] -> Either Pos [(Pos, Token)]
lexKeywordOrVar s p ts =
  let (v, rest) = lexVar s in
    if length v > 0 then trykw keywords v rest p ts else Left p
  where
    trykw (kwtok : kws) v s =
      if show kwtok == v then lexAdd v s kwtok else trykw kws v s
    trykw [] v s = lexAdd v s (TkVar v)

-- Add a token, and continue lexing
lexAdd :: String -> String -> Token -> Pos -> [(Pos, Token)] -> Either Pos [(Pos, Token)]
lexAdd t_s s t p ts = lexStrh s (forward' (length t_s) p) ((p, t) : ts)

-- Format for a lex error
lexErr (line, col) = Left $ "Lex error at line " ++ show line ++ ", column " ++ show col

-- Lex a string.
lexStr :: String -> Either String [(Pos, Token)]
lexStr s = either lexErr (Right . reverse) $ lexStrh s (1, 0) []

lexFile = lexStr
