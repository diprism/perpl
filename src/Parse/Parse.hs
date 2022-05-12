{- Parser code -}

module Parse.Parse where
import Parse.Lex
import Struct.Lib

-- Throws a lexer error message at a certain position
lexErr (line, col) = Left $ "Lex error at line " ++ show line ++ ", column " ++ show col

-- Throws a parser error message (s) at a certain position (p)
parseErr' p s = Left (p, s)

eofPos = (-1, 0)
eofErr = parseErr' eofPos "unexpected EOF"

-- Throws a parser error message (s) at the current position
parseErr s = ParseM $ \ ts ->
  let p = case ts of [] -> eofPos; ((p, _) : ts) -> p in
    Left (p, s)

-- Parse error message formatting
formatParseErr (line, col) emsg = Left $
  "Parse error at line " ++ show line ++
    ", column " ++ show col ++ ": " ++ emsg

-- Parsing monad: given the lexed tokens, returns either an error or (a, remaining tokens)
newtype ParseM a = ParseM ([(Pos, Token)] -> Either (Pos, String) (a, [(Pos, Token)]))

-- Extract the function from ParseM
parseMf (ParseM f) = f

-- Call a ParseM's function with some tokens
parseMt ts (ParseM f) = f ts

-- Given something and a list of tokens, return them in the ParseM monad
parseMr = curry Right

-- Try to parse the second arg, falling back to the first if fails
parseElse a' (ParseM a) =
  ParseM $ \ ts -> either (\ _ -> Right (a', ts)) Right (a ts)

-- ParseM instances:
instance Functor ParseM where
  fmap f (ParseM g) = ParseM $ \ ts -> g ts >>= \ p -> Right (f (fst p), snd p)

instance Applicative ParseM where
  pure = ParseM . parseMr
  ParseM f <*> ParseM g =
    ParseM $ \ ts -> f ts >>= \ p ->
    g (snd p) >>= \ p' ->
    Right (fst p (fst p'), snd p')

instance Monad ParseM where
  (ParseM f) >>= g = ParseM $ \ ts -> f ts >>= \ (a, ts') -> parseMf (g a) ts'

-- Peek at the next n tokens without consuming them
parsePeeks :: Int -> ParseM [Token]
parsePeeks n = ParseM $ \ ts -> if length ts < n then eofErr else parseMr [t | (_, t) <- take n ts] ts

-- Peek at the next token without consuming it
parsePeek :: ParseM Token
parsePeek = head <$> parsePeeks 1

-- Add semicolon to end of toks, if not already there
parseAddEOF :: ParseM ()
parseAddEOF =
  ParseM $ \ ts ->
  let ((lastrow, lastcol), lasttok) = last ts
  
      ts' = if lasttok == TkSemicolon then [] else [((lastrow, lastcol + 1), TkSemicolon)]
  in
    Right ((), ts ++ ts')

-- Drop the next token
parseEat :: ParseM ()
parseEat = ParseM $ \ ts -> case ts of
  [] -> eofErr
  (_ : ts') -> Right ((), ts')

-- Consume token t.
parseDrop t = parsePeek >>= \ t' ->
  if t == t' then parseEat else parseErr ("expecting " ++ show t)

-- Consume token t if there is one.
-- (can't use parsePeek because there could be an optional EOF token ';')
parseDropSoft t = ParseM $ \ ts -> case ts of
  ((_, t') : ts') -> parseMr () (if t == t' then ts' else ts)
  [] -> parseMr () ts

-- Parse a symbol.
parseVar :: ParseM Var
parseVar = parsePeek >>= \ t -> case t of
  TkVar v -> parseEat *> pure v
  _ -> parseErr (if t `elem` keywords then show t ++ " is a reserved keyword"
                  else "expected a variable name here")

-- Parse zero or more symbols.
parseVars :: ParseM [Var]
parseVars = parsePeek >>= \ t -> case t of
  TkVar v -> parseEat *> pure ((:) v) <*> parseVars
  _ -> pure []

-- Parse comma-delimited symbols
parseVarsCommas :: ParseM [Var]
parseVarsCommas = parsePeeks 2 >>= \ ts -> case ts of
  [TkVar v, TkComma] -> parseEat *> parseEat *> pure ((:) v) <*> parseVarsCommas
  [TkVar v, _] -> parseEat *> pure [v]
  _ -> parseErr "expecting a variable name here"

-- Parse a branch of a case expression.
parseCase :: ParseM CaseUs
parseCase = (*>) (parseDropSoft TkBar) $ parsePeek >>= \ t -> case t of
  TkVar c -> parseEat *> pure (CaseUs c) <*> parseVars <* parseDrop TkArr <*> parseTerm1
  _ -> parseErr "expecting another case"

-- Parse zero or more branches of a case expression.
parseCases :: ParseM [CaseUs]
parseCases = (*>) (parseDropSoft TkBar) $ parsePeek >>= \ t -> case t of
  TkVar _ -> pure (:) <*> parseCase <*> parseCases
  _ -> pure []

{-

TERM1 :=
  | case TERM1 of VAR VAR* -> TERM2 \| ...
  | if TERM1 then TERM1 else TERM1
  | \ VAR [: TYPE1]. TERM1
  | let (VAR, ...) = TERM1 in TERM1
  | let VAR = TERM1 in TERM1
  | TERM2

 -}

-- CaseOf, Lam, Let
parseTerm1 :: ParseM UsTm
parseTerm1 = parsePeeks 2 >>= \ t1t2 -> case t1t2 of
-- case term of term
  [TkCase, _] -> parseEat *> pure UsCase <*> parseTerm1 <* parseDrop TkOf <*> parseCases
-- if term then term else term
  [TkIf, _] -> parseEat *> pure UsIf <*> parseTerm1 <* parseDrop TkThen <*> parseTerm1 <* parseDrop TkElse <*> parseTerm1
-- \ x : type. term
  [TkLam, _] -> parseEat *> pure UsLam <*> parseVar <*> parseTpAnn <* parseDrop TkDot <*> parseTerm1
-- let (x, y, ...) = term in term
  [TkLet, TkParenL] -> parseEat *> parseEat *> pure (flip (UsElimProd Multiplicative)) <*> parseVarsCommas <* parseDrop TkParenR <* parseDrop TkEq <*> parseTerm1 <* parseDrop TkIn <*> parseTerm1
-- let <..., _, x, _, ...> = term in term
  [TkLet, TkLangle] -> parseEat *> parseEat *> pure (flip (UsElimProd Additive)) <*> parseVarsCommas <* parseDrop TkRangle <* parseDrop TkEq <*> parseTerm1 <* parseDrop TkIn <*> parseTerm1
-- let x = term in term
  [TkLet, _] -> parseEat *> pure UsLet <*> parseVar <*> parseTpAnn <* parseDrop TkEq
             <*> parseTerm1 <* parseDrop TkIn <*> parseTerm1
  _ -> parseTerm2


{-

TERM2 :=
  | amb TERM5*
  | factor weight in TERM2
  | fail : TYPE1
  | TERM4

 -}

parseTerm2 :: ParseM UsTm
parseTerm2 = parsePeek >>= \ t -> case t of
-- amb tm*
  TkAmb -> parseEat *> parseAmbs []
-- factor wt
  TkFactor -> parseEat *> pure UsFactor <*> parseNum <* parseDrop TkIn <*> parseTerm2
-- fail : type
  TkFail -> parseEat *> pure UsFail <*> parseTpAnn
  _ -> parseTerm4

-- Parse tok-delimited terms
parseTmsDelim :: Token -> [UsTm] -> ParseM [UsTm]
parseTmsDelim tok tms = parsePeek >>= \ t ->
  if t == tok
    then parseEat >> parseTerm1 >>= \ tm -> parseTmsDelim tok (tm : tms)
    else return (reverse tms)

-- Parses a (floating-point) number
parseNum :: ParseM Double
parseNum = parsePeek >>= \ t -> case t of
  TkNum o -> parseEat >> return o
  _ -> parseErr "Expected a number here"


{-

TERM4 :=
  | TERM5 == TERM5 == ...
  | TERM5 TERM5*
  | TERM5

 -}

parseTerm4 :: ParseM UsTm
parseTerm4 =
  parseTerm5 >>= \ tm ->
  parsePeek >>= \ t -> case t of
    TkDoubleEq -> UsEqs <$> parseTmsDelim TkDoubleEq [tm]
    _ -> parseTermApp tm

-- Parses the "tm*" part of "amb tm*"
parseAmbs :: [UsTm] -> ParseM UsTm
parseAmbs acc =
  parseElse (UsAmb (reverse acc)) (parseTerm5 >>= \ tm -> parseAmbs (tm : acc))

-- Parse an application spine
parseTermApp :: UsTm -> ParseM UsTm
parseTermApp acc =
  parseElse acc $ parseTerm5 >>= parseTermApp . UsApp acc

{-

TERM5 :=
  | VAR
  | (TERM1)
  | <TERM1, ...>
  | fail           (without type annotation)
  | error

 -}

-- Var, Parens
parseTerm5 :: ParseM UsTm
parseTerm5 = parsePeek >>= \ t -> case t of
  TkVar v -> parseEat *> pure (UsVar v)
  TkParenL -> parseEat *> (parseTerm1 >>= \ tm -> parseTmsDelim TkComma [tm] >>= \ tms -> pure (if length tms == 1 then tm else UsProd Multiplicative tms)) <* parseDrop TkParenR -- TODO: product
  TkLangle -> parseEat *> pure (UsProd Additive) <*> (parseTerm1 >>= \ tm -> parseTmsDelim TkComma [tm]) <* parseDrop TkRangle
  TkFail -> parseEat *> pure (UsFail NoTp)
  _ -> parseErr "couldn't parse a term here; perhaps add parentheses?"

-- Parses tok-delimited types
parseTpsDelim :: Token -> [Type] -> ParseM [Type]
parseTpsDelim tok acc = parsePeek >>= \ t ->
  if t == tok
    then (parseEat >> parseType3 >>= \ tp' -> parseTpsDelim tok (tp' : acc))
    else pure (reverse acc)


{- Type Annotation

TYPEANN :=
  | 
  | : TYPE1

-}

parseTpAnn :: ParseM Type
parseTpAnn =
  parsePeek >>= \ t -> if t == TkColon then (parseEat *> parseType1) else pure NoTp

{-

TYPE1 :=
  | TYPE2 -> TYPE1
  | TYPE2

 -}

-- Arrow
parseType1 :: ParseM Type
parseType1 = parseType2 >>= \ tp -> parsePeek >>= \ t -> case t of
  TkArr -> parseEat *> pure (TpArr tp) <*> parseType1
  _ -> pure tp

{-

TYPE2 :=
  | TYPE3 * TYPE3 * ...
  | TYPE3 & TYPE3 & ...
  | TYPE3

 -}

-- Product, Ampersand
parseType2 :: ParseM Type
parseType2 = parseType3 >>= \ tp -> parsePeek >>= \ t -> case t of
  TkStar  -> pure (TpProd Multiplicative) <*> parseTpsDelim TkStar [tp]
  TkAmp   -> pure (TpProd Additive) <*> parseTpsDelim TkAmp [tp]
  _ -> pure tp

{-

TYPE3 :=
  | VAR TYPE4...
  | TYPE4

 -}

-- TypeVar
parseType3 :: ParseM Type
parseType3 = parsePeek >>= \ t -> case t of
  TkVar v -> parseEat *> pure (TpVar v) <*> parseTypes
  _ -> parseType4

{-

TYPE4 :=
  | VAR
  | (TYPE1)
  | error

-}

parseType4 :: ParseM Type
parseType4 = parsePeek >>= \ t -> case t of
  TkVar v -> parseEat *> pure (TpVar v [])
  TkBool -> parseEat *> pure (TpVar "Bool" [])
  TkParenL -> parseEat *> parseType1 <* parseDrop TkParenR
  _ -> parseErr "couldn't parse a type here; perhaps add parentheses?"

-- List of Constructors
parseCtors :: ParseM [Ctor]
parseCtors = ParseM $ \ ts -> case ts of
  ((p, TkVar _) : _) -> parseMt ((p, TkBar) : ts) parseCtorsH
  _ -> parseMt ts parseCtorsH
parseCtorsH = parsePeek >>= \ t -> case t of
  TkBar -> parseEat *> pure (:) <*> (pure Ctor <*> parseVar <*> parseTypes) <*> parseCtorsH
  _ -> pure []

-- List of Types
parseTypes :: ParseM [Type]
parseTypes = parseElse [] (parseType4 >>= \ tp -> fmap ((:) tp) parseTypes)

-- Program
parseProg :: ParseM (Maybe UsProg)
parseProg = parsePeek >>= \ t -> case t of
-- define x : type = term; ...
  TkFun -> parseEat *> pure Just <*> (pure UsProgFun <*> parseVar <*> parseTpAnn
             <* parseDrop TkEq <*> parseTerm1 <* parseDrop TkSemicolon)
-- extern x : type; ...
  TkExtern -> parseEat *> pure Just <*> (pure UsProgExtern <*> parseVar <*> parseTpAnn
                <* parseDrop TkSemicolon)
-- data Y vars = ctors; ...
  TkData -> parseEat *> pure Just <*> (pure UsProgData <*> parseVar <*> parseVars <* parseDrop TkEq
              <*> parseCtors <* parseDrop TkSemicolon)
  _ -> pure Nothing

parseProgsUntil :: ParseM [UsProg]
parseProgsUntil = parseProg >>= maybe (pure []) (\ p -> pure ((:) p) <*> parseProgsUntil)

parseProgs :: ParseM UsProgs
parseProgs = pure UsProgs <*> parseProgsUntil <*> parseTerm1  <* parseDrop TkSemicolon

parseFormatErr :: [(Pos, Token)] -> Either (Pos, String) a -> Either String a
parseFormatErr ts (Left (p, emsg))
  | p == eofPos = formatParseErr (fst (last ts)) emsg
  | otherwise = formatParseErr p emsg
parseFormatErr ts (Right a) = Right a

-- Extract the value from a ParseM, if it consumed all tokens
parseOut :: ParseM a -> [(Pos, Token)] -> Either String a
parseOut m ts =
  parseFormatErr ts $
  parseMf m ts >>= \ (a, ts') ->
  if length ts' == 0
    then Right a
    else parseErr' (fst $ head $ drop (length ts - length ts' - 1) ts)
           "couldn't parse after this"

-- Parse a whole program.
parseFile :: [(Pos, Token)] -> Either String UsProgs
parseFile = parseOut (parseAddEOF >> parseProgs)
