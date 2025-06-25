{- Parser code -}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# HLINT ignore "Use $>" #-}
{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Use section" #-}
{-# HLINT ignore "Redundant fmap" #-}
{-# HLINT ignore "Use <$" #-}
{-# HLINT ignore "Use null" #-}
{-# HLINT ignore "Use >=>" #-}
{-# HLINT ignore "Use first" #-}
{-# HLINT ignore "Use list comprehension" #-}
{-# HLINT ignore "Use !!" #-}

module Parse.Parse where
import Parse.Lex
import Struct.Lib
import Util.Helpers (enumerate)

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

-- Parse one or more tok-delimited terms/types
parseDelim :: (ParseM a) -> Token -> [a] -> ParseM [a]
parseDelim m tok acc = parsePeek >>= \ t ->
  if t == tok
    then parseEat >> m >>= \ a -> parseDelim m tok (a : acc)
    else return (reverse acc)
         
-- Pipe-delimited list (the first pipe is optional)
parseBranches :: ParseM a -> ParseM [a]
parseBranches branch = parseDropSoft TkBar *> oneOrMore
  where oneOrMore = (:) <$> branch <*> zeroOrMore
        zeroOrMore = parsePeek >>= \ t -> case t of
          TkBar -> parseEat *> oneOrMore
          _ -> pure []

-- Parse a symbol.
parseVar :: ParseM String
parseVar = parsePeek >>= \ t -> case t of
  TkVar v -> parseEat *> pure v
  _ -> parseErr (if t `elem` keywords then show t ++ " is a reserved keyword"
                  else "expected a variable name here")

-- Parse zero or more symbols.
parseVars :: ParseM [String]
parseVars = parsePeek >>= \ t -> case t of
  TkVar v -> parseEat *> pure (v:) <*> parseVars
  _ -> pure []

-- Parse comma-delimited symbols
parseVarsCommas :: Token -> Bool -> Bool -> ParseM [String]
parseVarsCommas close allow0 allow1 = parsePeeks 2 >>= \ ts -> case ts of
  [TkVar v, TkComma] -> parseEat *> parseEat *> pure (v:) <*> parseVarsCommas close allow1 True
  [TkVar v, t] | t==close -> if allow1 then parseEat *> parseEat *> pure [v] else parseErr "unary tuple of variables not allowed here"
  [t, _] | t==close -> if allow0 then parseEat *> pure [] else parseErr "0-ary tuple of variables not allowed here"
  _ -> parseErr "expecting a tuple of variables"

-- Parse a branch of a case expression.
parseCase :: ParseM CaseUs
parseCase = parsePeek >>= \ t -> case t of
  TkVar c -> parseEat *> pure (CaseUs (TmN c) . map TmV) <*> parseVars <* parseDrop TkArr <*> parseTerm1
  _ -> parseErr "expecting a case"

-- Parse one or more branches of a case expression.
parseCases :: ParseM [CaseUs]
parseCases = parseBranches parseCase

-- Parses a floating-point number
parseDouble :: ParseM Double
parseDouble = parsePeek >>= \ t -> case t of
  TkDouble o -> parseEat >> return o
  _ -> parseErr "Expected a number here"

-- Parses a natural number
parseNat :: ParseM Int
parseNat = parsePeek >>= \ t -> case t of
  TkNat n -> parseEat >> return n
  _ -> parseErr "Expected a natural number here"

-- Parses a rational number
parseRatio :: ParseM Rational
parseRatio = parsePeek >>= \ t -> case t of
  TkRatio r -> parseEat >> return r
  _ -> parseErr "Expected a rational number here"

{-

TERM1 ::=
  | case TERM1 of VAR VAR* -> TERM1 \| ...
  | if TERM1 then TERM1 else TERM1
  | \ VAR [: TYPE1]. TERM1
  | let (VAR, ...) = TERM1 in TERM1
  | let VAR = TERM1 in TERM1
  | factor weight in TERM1
  | TERM2

 -}

-- CaseOf, Lam, Let
parseTerm1 :: ParseM UsTm
parseTerm1 = parsePeeks 2 >>= \ t1t2 -> case t1t2 of
-- case term of c term ... \| ...
  [TkCase, _] -> parseEat *> pure UsCase <*> parseTerm1 <* parseDrop TkOf <*> parseCases
-- if term then term else term
  [TkIf, _] -> parseEat *> pure UsIf <*> parseTerm1 <* parseDrop TkThen <*> parseTerm1 <* parseDrop TkElse <*> parseTerm1
-- \ x [: type] . term
  [TkLam, _] -> parseEat *> pure (UsLam . TmV) <*> parseVar <*> parseTpAnn <* parseDrop TkDot <*> parseTerm1
-- let (x, y, ...) = term in term
  [TkLet, TkParenL] -> do
    parseEat
    parseEat
    xs <- parseVarsCommas TkParenR True False
    parseDrop TkEq
    tm <- parseTerm1
    parseDrop TkIn
    tm' <- parseTerm1
    return (UsElimMultiplicative tm (map TmV xs) tm')
-- let <..., _, x, _, ...> = term in term
  [TkLet, TkLangle] -> do
    parseEat
    parseEat
    xs <- parseVarsCommas TkRangle False True
    case [ (i,x) | (i,x) <- enumerate xs, x /= "_" ] of
      [(i,x)] -> do
        parseDrop TkEq
        tm <- parseTerm1
        parseDrop TkIn
        tm' <- parseTerm1
        return (UsElimAdditive tm (length xs) i (TmV x) tm')
      _ -> parseErr "Expected exactly one non-underscore variable"
-- let x = term [: type] in term
  [TkLet, _] -> parseEat *> pure (UsLet . TmV) <*> parseVar <* parseDrop TkEq
             <*> parseTerm1 <* parseDrop TkIn <*> parseTerm1
-- factor wt
  [TkFactor, TkDouble x] -> parseEat *> pure UsFactorDouble <*> parseDouble <* parseDrop TkIn <*> parseTerm1
  [TkFactor, TkNat x] -> parseEat *> pure UsFactorNat <*> parseNat <* parseDrop TkIn <*> parseTerm1
  [TkFactor, TkRatio x] -> parseEat *> pure UsFactorRatio <*> parseRatio <* parseDrop TkIn <*> parseTerm1
  _ -> parseTerm2


{-

TERM2 ::=
  | TERM3 [: TYPE1]

Currently the only term that can have a type annotation is "fail".

 -}

parseTerm2 :: ParseM UsTm
parseTerm2 = parseTerm3 >>= \ tm ->
  case tm of
    UsFail NoTp -> pure UsFail <*> parseTpAnn
    _ -> return tm


{-

TERM3 ::=
  | TERM4 == TERM4 == ...

-}


parseTerm3 :: ParseM UsTm
parseTerm3 = parseTerm4 >>= \ tm ->
  parsePeek >>= \ t -> case t of
    TkDoubleEq -> UsEqs <$> parseDelim parseTerm4 TkDoubleEq [tm]
    _ -> return tm


{-

TERM4 ::=
  | TERM5 TERM5*
  | amb TERM5*
  | TERM5

 -}

parseTerm4 :: ParseM UsTm
parseTerm4 = parsePeek >>= \ t -> case t of
-- amb tm*
  TkAmb -> parseEat *> parseAmbs []
  _ -> parseTerm5 >>= \ tm -> parseTermApp tm

-- Parses the "tm*" part of "amb tm*"
parseAmbs :: [UsTm] -> ParseM UsTm
parseAmbs acc =
  parseElse (UsAmb (reverse acc)) (parseTerm5 >>= \ tm -> parseAmbs (tm : acc))

-- Parse an application spine
parseTermApp :: UsTm -> ParseM UsTm
parseTermApp acc =
  parseElse acc $ parseTerm5 >>= parseTermApp . UsApp acc

{-

TERM5 ::=
  | VAR                      variable
  | (TERM1)                  grouping
  | ()                       multiplicative tuple of zero terms
  | (TERM1+)                 multiplicative tuple of two or more terms
  | <TERM1*>                 additive tuple of zero or more terms
  | CONST                    constant (natural number)
  | fail                     (without type annotation)
  | error

 -}

-- Var, Parens
parseTerm5 :: ParseM UsTm
parseTerm5 = parsePeek >>= \ t -> case t of
  TkVar "_" -> parseErr "Expected non-underscore variable here"
  TkVar v -> parseEat *> pure (UsVar (TmV v))
  TkParenL -> parseEat *> (
    parsePeek >>= \ t -> case t of
        TkParenR -> pure (UsProd Multiplicative [])
        _ -> parseTerm1 >>= \ tm -> parseDelim parseTerm1 TkComma [tm] >>= \ tms -> pure (if length tms == 1 then tm else UsProd Multiplicative tms)
    ) <* parseDrop TkParenR
  TkLangle -> parseEat *> (
    parsePeek >>= \ t -> case t of
        TkRangle -> pure (UsProd Additive [])
        _ -> pure (UsProd Additive) <*> (parseTerm1 >>= \ tm -> parseDelim parseTerm1 TkComma [tm])) <* parseDrop TkRangle
  TkNat n -> parseEat *> pure (unpackNat n)
  TkFail -> parseEat *> pure (UsFail NoTp)
  _ -> parseErr "couldn't parse a term here; perhaps add parentheses?"

-- Unpack a natural number into a series of successors
unpackNat :: Int -> UsTm
unpackNat k =
  if k > 0 then (UsApp (UsVar (TmV "Succ")) (unpackNat (k-1)))
  else (UsVar (TmV "Zero"))

{- Type Annotation

TYPEANN ::=
  | 
  | : TYPE1

-}

parseTpAnn :: ParseM Type
parseTpAnn =
  parsePeek >>= \ t -> if t == TkColon then (parseEat *> parseType1 []) else pure NoTp

{-

TYPE1 ::=
  | TYPE2 -> TYPE1              function
  | TYPE2

 -}

-- Arrow
parseType1 :: [TpVar] -> ParseM Type
parseType1 ps = parseType2 ps >>= \ tp -> parsePeek >>= \ t -> case t of
  TkArr -> parseEat *> pure (TpArr tp) <*> parseType1 ps
  _ -> pure tp


{-

TYPE2 ::=
  | VAR TYPE3 ...               type application (e.g., List Nat)
  | TYPE3

 -}

-- TypeVar
parseType2 :: [TpVar] -> ParseM Type
parseType2 ps = parsePeek >>= \ t -> case t of
  TkVar v -> parseEat *> if TpV v `elem` ps then pure (TpVar (TpV v)) else pure (TpData (TpN v) []) <*> parseTypes ps
  _ -> parseType3 ps


{-

TYPE3 ::=
  | ()                          multiplicative product
  | (TYPE1)                     grouping
  | (TYPE1, TYPE1, TYPE1*)      multiplicative product
  | <TYPE1*>                    additive product
  | Bool                        built-in type names
  | VAR                         datatype without argument

 -}

parseType3 :: [TpVar] -> ParseM Type
parseType3 ps = parsePeek >>= \ t -> case t of
  TkParenL -> parseEat *> (
    parsePeek >>= \ t -> case t of
        TkParenR -> pure (TpProd Multiplicative [])
        _ -> parseType1 ps >>= \ tp -> parseDelim (parseType1 ps) TkComma [tp] >>= \ tps -> pure (if length tps == 1 then tp else TpProd Multiplicative tps)
    ) <* parseDrop TkParenR
  TkLangle -> parseEat *> (
    parsePeek >>= \ t -> case t of
        TkRangle -> pure (TpProd Additive [])
        _ -> pure (TpProd Additive) <*> (parseType1 ps >>= \ tp -> parseDelim (parseType1 ps) TkComma [tp])) <* parseDrop TkRangle
  TkBool -> parseEat *> pure tpBool
  TkVar v -> parseEat *> pure (if TpV v `elem` ps then TpVar (TpV v) else TpData (TpN v) [] [])
  _ -> parseErr "couldn't parse a type here; perhaps add parentheses?"

-- List of Constructors
parseEqCtors :: [TpVar] -> ParseM [Ctor]
parseEqCtors ps = parsePeek >>= \t -> case t of
  TkEq -> parseDrop TkEq *> parseBranches (pure (Ctor . TmN) <*> parseVar <*> parseTypes ps)
  TkSemicolon -> return []
  _ -> parseErr "expected = or ;"

-- List of Types
parseTypes :: [TpVar] -> ParseM [Type]
parseTypes ps = parseElse [] (parseType3 ps >>= \ tp -> fmap ((:) tp) (parseTypes ps))

{-

PROG ::=
  | define VAR ... [: TYPE1] = TERM1;
  | extern VAR [: TYPE1];
  | data VAR VAR ... = VAR TYPE1 ... \| ...;

-}

-- Program
parseProg :: ParseM (Maybe UsProg)
parseProg = parsePeek >>= \ t -> case t of
-- define x [: type] = term; ...
  TkFun -> parseEat *> pure Just <*>
       (parseVar >>= \ x ->
        fmap (map TmV) parseVars >>= \xs ->
        parseTpAnn >>= \ tp ->
        parseDrop TkEq >>
        parseTerm1 >>= \ tm ->
        pure (UsProgDefine (TmN x) (joinUsLams xs tm) tp) <* parseDrop TkSemicolon)
-- extern x [: type]; ...
  TkExtern -> parseEat *> pure Just <*> (pure (UsProgExtern . TmN) <*> parseVar <*> parseTpAnn
                <* parseDrop TkSemicolon)
-- data Y vars = ctors; ...
  TkData -> parseEat *> pure Just <*>
       (fmap TpN parseVar >>= \f ->
        fmap (map TpV) parseVars >>= \ps ->
        pure (UsProgData f ps) <*> parseEqCtors ps <* parseDrop TkSemicolon)
  _ -> pure Nothing

parseProgsUntil :: ParseM [UsProg]
parseProgsUntil = parseProg >>= maybe (pure []) (\ p -> pure ((:) p) <*> parseProgsUntil)

{-

PROGS ::= PROG ... TERM1

-}

parseProgs :: ParseM UsProgs
parseProgs = pure UsProgs <*> parseProgsUntil <*> parseTerm1 <* parseDrop TkSemicolon

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
