{- Lexer code -}

module Parse.Lex (Token (..), keywords, Pos, lexFile) where
import Data.Char (isAlpha, isDigit, isSpace)
import Text.Read ( readMaybe )
import Data.Ratio ( (%) )

-- Possible tokens
data Token =
    TkVar String -- "x"
  | TkDouble Double -- floating-point literal
  | TkNat Int -- natural number
  | TkRatio Rational -- rational number
  -- Punctuation tokens
  | TkLam -- "\"
  | TkParenL -- "("
  | TkParenR -- ")"
  | TkEq -- "="
  | TkArr -- "->"
  | TkColon -- ":"
  | TkDot -- "."
  | TkComma -- ","
  | TkLangle -- "<"
  | TkRangle -- ">"
  | TkBar -- "|"
  | TkSemicolon -- ";"
  | TkDoubleEq -- "=="
  | TkAdd -- "+"
  -- Keyword tokens
  | TkFail -- "fail"
  | TkAmb -- "amb"
  | TkFactor -- "factor"
  | TkCase -- "case"
  | TkOf -- "of"
  | TkLet -- "let"
  | TkIn -- "in"
  | TkFun -- "define"
  | TkExtern -- "extern"
  | TkData -- "data"
  | TkBool -- "Bool"
  | TkIf -- "if"
  | TkThen -- "then"
  | TkElse -- "else"
  deriving Eq

instance Show Token where
  show :: Token -> String
  show (TkVar x) = x
  show (TkDouble d) = show d
  show (TkNat n) = show n
  show (TkRatio r) = show r
  -- Punctuation tokens
  show TkLam = "\\"
  show TkParenL = "("
  show TkParenR = ")"
  show TkEq = "="
  show TkArr = "->"
  show TkColon = ":"
  show TkDot = "."
  show TkComma = ","
  show TkLangle = "<"
  show TkRangle = ">"
  show TkBar = "|"
  show TkSemicolon = ";"
  show TkDoubleEq = "=="
  show TkAdd = "+"
  -- Keyword tokens
  show TkFail = "fail"
  show TkAmb = "amb"
  show TkFactor = "factor"
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


type Pos = (Int, Int) -- Line, column

-- Increments column by n
forward' :: Int -> Pos -> Pos
forward' n (line, column) = (line, column + n)

-- Increments column by 1
forward :: Pos -> Pos
forward = forward' 1

-- Goes to the next line
next :: Pos -> Pos
next (line, column) = (succ line, 1)

-- List of punctuation tokens
punctuation :: [Token]
punctuation = [TkLam, TkParenL, TkParenR, TkDoubleEq, TkEq, TkArr, TkColon, TkDot, TkComma, TkBar, TkSemicolon, TkLangle, TkRangle, TkAdd]
-- List of keyword tokens (use alphanumeric chars)
keywords :: [Token]
keywords = [TkAmb, TkFactor, TkFail, TkCase, TkOf, TkLet, TkIn, TkFun, TkExtern, TkData, TkBool, TkVar "True", TkVar "False", TkIf, TkThen, TkElse]

-- Tries to lex s as punctuation, otherwise lexing s as a keyword or a var
lexPunctuation :: String -> Pos -> [(Pos, Token)] -> Either (Pos, String) [(Pos, Token)]
lexPunctuation s =
  foldr (\ t owise -> maybe owise (flip (lexAdd (show t)) t) (prefix (show t) s))
        (lexNum s)
        punctuation
  where
    prefix (tc : tcs) (c : cs) =
      if tc == c then prefix tcs cs else Nothing
    prefix [] s = Just s
    prefix _ [] = Nothing


-- Lex a string, returning a list of tokens
lexStrh :: String -> Pos -> [(Pos, Token)] -> Either (Pos, String) [(Pos, Token)]
lexStrh (' ' : s) = lexStrh s . forward
lexStrh ('\t' : s) = lexStrh s . (forward' 8)
lexStrh ('\r' : '\n' : s) = lexStrh s . next
lexStrh ('\n' : s) = lexStrh s . next
lexStrh ('\r' : s) = lexStrh s . next
lexStrh ('-' : '-' : s) = lexComment Nothing s
lexStrh ('{' : '-' : s) = lexComment (Just 0) s
lexStrh ('-' : '}' : s) = \ p _ -> Left (p, "unexpected end-of-comment '-}'")
lexStrh "" = \ _ ts -> Right ts
lexStrh s = lexPunctuation s

-- Lex a comment.
-- lexComment Nothing scans a comment from -- to the end of the line.
-- lexComment (Just n) scans a nested comment (inside {- and -}).
lexComment :: Maybe Integer -> String -> Pos -> [(Pos, Token)] -> Either (Pos, String) [(Pos, Token)]
lexComment Nothing  ('\n' : s) = lexStrh s . next
lexComment (Just n) ('\n' : s) = lexComment (Just n) s . next
lexComment (Just 0) ('-' : '}' : s) = lexStrh s . forward' 2
lexComment (Just n) ('-' : '}' : s) = lexComment (Just (pred n)) s . forward' 2
lexComment (Just n) ('{' : '-' : s) = lexComment (Just (succ n)) s . forward' 2
lexComment multiline (_ : s) = lexComment multiline s . forward
lexComment _ "" = \ _ ts -> Right ts

-- Lex a number (will be either a Natural Number or a Double)
lexNum :: String -> Pos -> [(Pos, Token)] -> Either (Pos, String) [(Pos, Token)]
lexNum s = case span isDigit s of -- read until we encounter a non-digit
  ([], _) -> lexKeywordOrVar s
  (numStr, rest1) -> case dropWhile isSpace rest1 of -- drop any spaces between numbers
    '/':rest2 -> -- Case: rational number detected
      case span isDigit rest2 of
        ([], _) -> \ p _ -> Left (p, "Incomplete rational number detected") -- ex: 7/ versus 7/2
        (denomStr, rest3) ->
          case readMaybe numStr :: Maybe Integer of
            Nothing -> \ p _ -> Left (p, "Numerator must be Integer") -- this shouldn't be able to happen
            Just numerator -> case readMaybe denomStr :: Maybe Integer of
              Nothing -> \ p _ -> Left (p, "Denominator must be Integer") -- this shouldn't be able to happen
              Just denominator ->
                let ratio = numerator % denominator
                in lexAdd (take (length s - length rest3) s) rest3 (TkRatio ratio)
    _ -> case reads s :: [(Double, String)] of -- if no '/' detected (aka a number but not rational)
      [] -> lexKeywordOrVar s -- Case: unable to be read as a double
      [(d, rest4)] -> if d < 0
        then \ p _ -> Left (p, "Negative number detected")
        else case reads s :: [(Int, String)] of
          [] -> if d == fromInteger (round d)
            then lexAdd (take (length s - length rest4) s) rest4 (TkNat (round d)) -- Special Case: double and int but not caught by reads (ex: 2.000)
            else lexAdd (take (length s - length rest4) s) rest4 (TkDouble d) -- Case: double, not int
          [(n, rest5)] -> 
            lexAdd (take (length s - length rest4) s) rest4 (TkNat n) -- Case: double and int (so treat as int)

-- Consumes characters until a non-variable character is reached
lexVar :: String -> (String, String)
lexVar "" = ("", "")
lexVar (c : s)
  | isVarFirstChar c = h [c] s
  | otherwise = ("", (c : s))
  where
    h v "" = (reverse v, "")
    h v (c : s)
      | isVarChar c = h (c : v) s
      | otherwise = (reverse v, (c : s))

-- Determines if c is a valid character for a variable name
isVarFirstChar :: Char -> Bool
isVarFirstChar c = '_' == c || isAlpha c
  
isVarChar :: Char -> Bool
isVarChar c = '\'' == c || isVarFirstChar c || isDigit c

-- Lex a keyword or a variable name
lexKeywordOrVar :: String -> Pos -> [(Pos, Token)] -> Either (Pos, String) [(Pos, Token)]
lexKeywordOrVar s p ts =
  case lexVar s of
    (v@(_:_), rest) -> trykw keywords v rest p ts
    ("", next:_) -> Left (p, "unexpected character '" ++ [next] ++ "'")
    ("", "") -> Left (p, "unexpected end of file (this shouldn't happen)")
  where
    trykw (kwtok : kws) v s =
      if show kwtok == v then lexAdd v s kwtok else trykw kws v s
    trykw [] v s = lexAdd v s (TkVar v)

{- Add a token to output token list and continue lexing

- t_s: new token as string
- s: rest of string after t_s
- t: new token as Token
- p: position of t
- ts: token list -}

lexAdd :: String -> String -> Token -> Pos -> [(Pos, Token)] -> Either (Pos, String) [(Pos, Token)]
lexAdd t_s s t p ts = lexStrh s (forward' (length t_s) p) ((p, t) : ts)

-- Format for a lex error
lexErr :: (Pos, String) -> String
lexErr ((line, col), msg) = "error at line " ++ show line ++ ", column " ++ show col ++ ": " ++ msg

-- Lex a string.
lexStr :: String -> Either String [(Pos, Token)]
lexStr s = either (Left . lexErr) (Right . reverse) $ lexStrh s (1, 1) []

-- Synonym for lexStr
lexFile = lexStr
