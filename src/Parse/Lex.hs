{- Lexer code -}

module Parse.Lex where
import Struct.Lib

-- Possible tokens
data Token =
    TkVar Var -- "x"
  | TkNum Int -- not sure if this is used anymore...
  | TkLam -- "\"
  | TkParenL -- "("
  | TkParenR -- ")"
  | TkEq -- "="
  | TkSample -- "sample"
  | TkFail -- "fail"
  | TkAmb -- "amb"
  | TkUni -- "uniform"
  | TkCase -- "case"
  | TkOf -- "of"
  | TkLet -- "let"
  | TkIn -- "in"
  | TkArr -- "->"
  | TkLeftArr -- "<-"
  | TkAmp -- "&"
  | TkStar -- "*"
  | TkColon -- ":"
  | TkDot -- "."
  | TkComma -- ","
  | TkLangle -- "<"
  | TkRangle -- ">"
  | TkBar -- "|"
  | TkSemicolon -- ";"
  | TkFun -- "define"
  | TkExtern -- "extern"
  | TkData -- "data"
  | TkBool -- "Bool"
  | TkIf -- "if"
  | TkThen -- "then"
  | TkElse -- "else"
  | TkDoubleEq -- "=="
  | TkUnit -- "Unit"
  deriving Eq

instance Show Token where
  show (TkVar x) = x
  show (TkNum n) = show n
  -- Punctuation tokens
  show TkLam = "\\"
  show TkParenL = "("
  show TkParenR = ")"
  show TkEq = "="
  show TkArr = "->"
  show TkLeftArr = "<-"
  show TkAmp = "&"
  show TkStar = "*"
  show TkColon = ":"
  show TkDot = "."
  show TkComma = ","
  show TkLangle = "<"
  show TkRangle = ">"
  show TkBar = "|"
  show TkSemicolon = ";"
  show TkDoubleEq = "=="
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
  show TkBool = "Bool"
  show TkIf = "if"
  show TkThen = "then"
  show TkElse = "else"
  show TkUnit = "Unit"


type Pos = (Int, Int) -- Line, column

-- Increments column by n
forward' :: Int -> Pos -> Pos
forward' n (line, column) = (line, column + n)

-- Increments column by 1
forward :: Pos -> Pos
forward = forward' 1

-- Goes to the next line
next :: Pos -> Pos
next (line, column) = (succ line, 0)

-- List of punctuation tokens
punctuation = [TkLam, TkParenL, TkParenR, TkDoubleEq, TkEq, TkArr, TkLeftArr, TkColon, TkDot, TkComma, TkBar, TkSemicolon, TkStar, TkAmp, TkLangle, TkRangle]
-- List of keyword tokens (use alphanumeric chars)
keywords = [TkFail, TkAmb, TkUni, TkCase, TkOf, TkLet, TkIn, TkUni, TkSample, TkFun, TkExtern, TkData, TkBool, TkVar "True", TkVar "False", TkIf, TkThen, TkElse, TkUnit]

-- Tries to lex s as punctuation, otherwise lexing s as a keyword or a var
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
  ('a' <= c && c <= 'z') ||
  ('A' <= c && c <= 'Z') ||
  ('0' <= c && c <= '9') ||
  ('\'' == c) || ('_' == c)

-- Lex a keyword or a variable name
lexKeywordOrVar :: String -> Pos -> [(Pos, Token)] -> Either Pos [(Pos, Token)]
lexKeywordOrVar s p ts =
  let (v, rest) = lexVar s in
    if length v > 0 then trynum v rest (trykw keywords v rest) p ts else Left p
  where
    trynum v s kw = if all (\ c -> '0' <= c && c <= '9') v then lexAdd v s (TkNum (read v :: Int)) else kw
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

-- Synonym for lexStr
lexFile = lexStr
