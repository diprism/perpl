module Parse where
import Exprs
import Lex

lexErr (line, col) = Left $ "Lex error at line " ++ show line ++ ", column " ++ show col

parseErr' p s = Left (p, s)

eofPos = (-1, 0)
eofErr = parseErr' eofPos "unexpected EOF"

parseErr s = ParseM $ \ ts ->
  let p = case ts of [] -> eofPos; ((p, _) : ts) -> p in
    Left (p, s)

formatParseErr (line, col) emsg = Left $
  "Parse error at line " ++ show line ++
    ", column " ++ show col ++ ": " ++ emsg

-- Parsing monad
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

parseSwitch :: (Token -> ParseM a) -> ParseM a
parseSwitch f = ParseM $ \ ts -> case ts of
  [] -> eofErr
  ((p, t) : ts) -> parseMt ((p, t) : ts) (f t)

-- Drop the next token
parseEat :: ParseM ()
parseEat = ParseM $ \ ts -> case ts of
  [] -> eofErr
  (_ : ts') -> Right ((), ts')

-- Consume token t.
parseDrop t = parseSwitch $ \ t' ->
  if t == t' then parseEat else parseErr ("expecting " ++ show t)

-- Consume token t if there is one.
-- (can't use parseSwitch because there could be an optional EOF token ';')
parseDropSoft t = ParseM $ \ ts -> case ts of
  ((_, t') : ts') -> parseMr () (if t == t' then ts' else ts)
  [] -> parseMr () ts

-- Parse a symbol.
parseVar :: ParseM Var
parseVar = parseSwitch $ \ t -> case t of
  TkVar v -> parseEat *> pure v
  _ -> parseErr (if t `elem` keywords then show t ++ " is a reserved keyword"
                  else "expected a variable name here")

-- Parse zero or more symbols.
parseVars :: ParseM [Var]
parseVars = parseSwitch $ \ t -> case t of
  TkVar v -> parseEat *> pure ((:) v) <*> parseVars
  _ -> pure []

-- Parse a branch of a case expression.
parseCase :: ParseM CaseUs
parseCase = (*>) (parseDropSoft TkBar) $ parseSwitch $ \ t -> case t of
  TkVar c -> parseEat *> pure (CaseUs c) <*> parseVars <* parseDrop TkArr <*> parseTerm2
  _ -> parseErr ("expecting another case")

-- Parse zero or more branches of a case expression.
parseCases :: ParseM [CaseUs]
parseCases = (*>) (parseDropSoft TkBar) $ parseSwitch $ \ t -> case t of
  TkVar _ -> pure (:) <*> parseCase <*> parseCases
  _ -> pure []

-- CaseOf
parseTerm1 :: ParseM UsTm
parseTerm1 = parseSwitch $ \ t -> case t of
-- case term of term
  TkCase -> parseEat *> pure UsCase <*> parseTerm1 <* parseDrop TkOf <*> parseCases
  _ -> parseTerm2

parseLamArgs :: ParseM [(Var, Type)]
parseLamArgs =
  pure (curry (:)) <*> parseVar <* parseDrop TkColon <*> parseType1
    <*> parseElse [] (parseDrop TkComma >> parseLamArgs)

-- Lam, Sample, Let
parseTerm2 :: ParseM UsTm
parseTerm2 = parseSwitch $ \ t -> case t of
-- \ x : type. term
  TkLam -> parseEat *> pure (flip (foldr (uncurry UsLam))) <*> parseLamArgs <* parseDrop TkDot <*> parseTerm1
    -- parseEat *> pure UsLam <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseTerm1
-- sample dist : type
  TkSample -> parseEat *> pure UsSamp <*> parseDist <* parseDrop TkColon <*> parseType1
-- let x = term in term
  TkLet -> parseEat *> pure UsLet <*> parseVar <* parseDrop TkEq
             <*> parseTerm1 <* parseDrop TkIn <*> parseTerm1
  _ -> parseTerm3

-- App
parseTerm3 :: ParseM UsTm
parseTerm3 = parseTerm4 >>= parseTermApp

-- Parse an application spine
parseTermApp tm =
  parseElse tm $ parseTerm4 >>= parseTermApp . UsApp tm

-- Var, Parens
parseTerm4 :: ParseM UsTm
parseTerm4 = parseSwitch $ \ t -> case t of
  TkVar v -> parseEat *> pure (UsVar v)
  TkParenL -> parseEat *> parseTerm1 <* parseDrop TkParenR
  _ -> parseErr "couldn't parse a term here; perhaps add parentheses?"

-- Arrow
parseType1 :: ParseM Type
parseType1 = parseType2 >>= \ tp -> parseSwitch $ \ t -> case t of
  TkArr -> parseEat *> pure (TpArr tp) <*> parseType1
  _ -> pure tp

-- If we ever add type apps or infix types (+, *), do them here
parseType2 :: ParseM Type
parseType2 = parseType3
{-parseType2 = parseType3 >>= tp -> parseSwitch $ \ t -> case t of
  TkPlus -> parseEat *> pure (TpSum tp) <*> parseType3
  _ -> pure tp-}

-- TypeVar
parseType3 :: ParseM Type
parseType3 = parseSwitch $ \ t -> case t of
  TkVar v -> parseEat *> pure (TpVar v)
  TkParenL -> parseEat *> parseType1 <* parseDrop TkParenR
  _ -> parseErr "couldn't parse a type here; perhaps add parentheses?"

-- List of Constructors
parseCtors :: ParseM [Ctor]
parseCtors = ParseM $ \ ts -> case ts of
  ((p, TkVar _) : _) -> parseMt ((p, TkBar) : ts) parseCtorsH
  _ -> parseMt ts parseCtorsH
parseCtorsH = parseSwitch $ \ t -> case t of
  TkBar -> parseEat *> pure (:) <*> (pure Ctor <*> parseVar <*> parseTypes) <*> parseCtorsH
  _ -> pure []

-- Dist
parseDist :: ParseM Dist
parseDist = parseSwitch $ \ t -> case t of
  TkAmb  -> parseEat *> pure DistAmb
  TkFail -> parseEat *> pure DistFail
  TkUni  -> parseEat *> pure DistUni
  _ -> parseErr ("expected one of " ++ show TkAmb ++ ", " ++ show TkFail ++ ", or " ++ show TkUni ++ " here")

-- List of Types
parseTypes :: ParseM [Type]
parseTypes = parseElse [] (parseType3 >>= \ tp -> fmap ((:) tp) parseTypes)

-- Program
parseProg :: ParseM UsProgs
parseProg = parseSwitch $ \ t -> case t of
-- define x : type = term; ...
  TkFun -> parseEat *> pure UsProgFun <*> parseVar <* parseDrop TkColon <*> parseType1
             <* parseDrop TkEq <*> parseTerm1 <* parseDrop TkSemicolon <*> parseProg
-- extern x : type; ...
  TkExtern -> parseEat *> pure UsProgExtern <*> parseVar <* parseDrop TkColon
                <*> parseType1 <* parseDrop TkSemicolon <*> parseProg
-- data Y = ctors; ...
  TkData -> parseEat *> pure UsProgData <*> parseVar <* parseDrop TkEq
              <*> parseCtors <* parseDrop TkSemicolon <*> parseProg
-- term
  _ -> pure UsProgExec <*> parseTerm1 <* parseDropSoft TkSemicolon

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

-- Parse a term
parseTerm :: String -> Either String UsTm
parseTerm s = lexStr s >>= parseOut parseTerm1

-- Parse a type
parseType :: String -> Either String Type
parseType s = lexStr s >>= parseOut parseType1

-- Parse a whole program.
parseFile :: String -> Either String UsProgs
parseFile s = lexStr s >>= parseOut parseProg
