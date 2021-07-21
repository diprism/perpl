module Parse where
import Exprs
import Lex

lexErr (line, col) = Left $ "Lex error at line " ++ show line ++ ", column " ++ show col

parseErr p s = Left (p, s)

formatParseErr (line, col) emsg = Left $
  "Parse error at line " ++ show line ++
    ", column " ++ show col ++ ": " ++ emsg

eofPos = (-1, 0)
eofErr = parseErr eofPos "unexpected EOF"

-- Parsing monad
newtype ParseM a = ParseM ([(Pos, Token)] -> Either (Pos, String) (a, [(Pos, Token)]))

-- Extract the function from ParseM
parseMf (ParseM f) = f

-- Call a ParseM's function with some tokens
parseMt ts (ParseM f) = f ts

-- Given something and a list of tokens, return them in the ParseM monad
parseMr = curry Right

-- Consume token t.
parseDrop t = ParseM $ \ ts -> case ts of
  ((p, t') : ts') -> if t == t' then parseMr () ts' else parseErr p ("expecting " ++ show t)
  [] -> eofErr

-- Consume token t if there is one.
parseDropSoft t = ParseM $ \ ts -> case ts of
  ((_, t') : ts') -> parseMr () (if t == t' then ts' else ts)
  [] -> parseMr () ts

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

-- Parse a symbol.
parseVar :: ParseM Var
parseVar = ParseM $ \ ts -> case ts of
  ((p, TkVar v) : ts) -> parseMr v ts
  ((p, t) : _) ->
    parseErr p (if t `elem` keywords then show t ++ " is a reserved keyword"
                 else "expected a variable name here")
  [] -> eofErr

-- Parse zero or more symbols.
parseVars :: ParseM [Var]
parseVars = ParseM $ \ ts -> case ts of
  ((p, TkVar v) : ts) -> parseMt ts $ pure ((:) v) <*> parseVars
  _ -> parseMr [] ts

-- Parse a branch of a case expression.
parseCase :: ParseM CaseUs
parseCase = ParseM $ \ ts -> case ts of
  ((p, TkBar) : ts) -> parseMt ts parseCase
  ((p, TkVar c) : ts) -> parseMt ts $ pure (CaseUs c) <*> parseVars <* parseDrop TkArr <*> parseTerm2

-- Parse zero or more branches of a case expression.
parseCases :: ParseM [CaseUs]
parseCases = (*>) (parseDropSoft TkBar) $ ParseM $ \ ts -> case ts of
  ((_, TkVar _) : _) -> parseMt ts $ pure (:) <*> parseCase <*> parseCases
  _ -> parseMr [] ts

-- CaseOf
parseTerm1 :: ParseM UsTm
parseTerm1 = ParseM $ \ ts -> case ts of
-- case term of cases
  ((p, TkCase) : ts) -> parseMt ts $ pure UsCase <*> parseTerm1 <* parseDrop TkOf <*> parseCases
  _ -> parseMt ts parseTerm2

parseLamArgs :: ParseM [(Var, Type)]
parseLamArgs =
  pure (curry (:)) <*> parseVar <* parseDrop TkColon <*> parseType1
    <*> parseElse [] (parseDrop TkComma >> parseLamArgs)

-- Lam, Sample, Let
parseTerm2 :: ParseM UsTm
parseTerm2 = ParseM $ \ ts -> case ts of
-- \ x : type. term
  ((p, TkLam) : ts) -> parseMt ts $ pure UsLam <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseTerm1
-- sample dist : type
  ((p, TkSample) : ts) -> parseMt ts $ pure UsSamp <*> parseDist <* parseDrop TkColon <*> parseType1
-- let x = term in term
  ((p, TkLet) : ts) -> parseMt ts $ pure UsLet <*> parseVar <* parseDrop TkEq <*> parseTerm1 <* parseDrop TkIn <*> parseTerm1
  _ -> parseMt ts parseTerm3

-- App
parseTerm3 :: ParseM UsTm
parseTerm3 = ParseM $ \ ts -> parseMt ts parseTerm4 >>= uncurry (parseMf . parseTermApp)

-- Parse an application spine
parseTermApp tm =
  parseElse tm (parseTerm4 >>= parseTermApp . UsApp tm)

-- Var, Parens
parseTerm4 :: ParseM UsTm
parseTerm4 = ParseM $ \ ts -> case ts of
  ((p, TkVar v) : ts) -> parseMr (UsVar v) ts
  ((p, TkParenL) : ts) -> parseMt ts $ parseTerm1 <* parseDrop TkParenR
  ((p, _) : _) -> parseErr p "couldn't parse a term here; perhaps you need to add parentheses?"
  [] -> eofErr


-- Arrow
parseType1 :: ParseM Type
parseType1 = ParseM $ \ ts -> parseMt ts parseType2 >>= \ (tp, ts) -> case ts of
  ((p, TkArr) : ts) -> parseMt ts $ pure (TpArr tp) <*> parseType1
  _ -> parseMr tp ts

-- If we ever add type apps, do them here
parseType2 :: ParseM Type
parseType2 = parseType3
{-
parseType2 = ParseM $ \ ts -> parseMt ts parseType3 >>= \ (tp, ts') -> case ts' of
  (TkPlus : ts') -> parseMt ts' $ pure (TpSum tp) <*> parseType3
  _ -> parseMr tp ts'
-}

-- TypeVar
parseType3 :: ParseM Type
parseType3 = ParseM $ \ ts -> case ts of
  ((p, TkVar v) : ts) -> parseMr (TpVar v) ts
  ((p, TkParenL) : ts) -> parseMt ts $ parseType1 <* parseDrop TkParenR
  ((p, _) : ts) -> parseErr p "couldn't parse a type here; perhaps you need to add parentheses?"
  [] -> eofErr

-- List of Constructors
parseCtors :: ParseM [Ctor]
parseCtors = ParseM $ \ ts -> case ts of
  ((p, TkVar _) : _) -> parseMt ((p, TkBar) : ts) parseCtorsH
  _ -> parseMt ts parseCtorsH
parseCtorsH = ParseM $ \ ts -> case ts of
  ((p, TkBar) : ts) -> parseMt ts $ pure (:) <*> (pure Ctor <*> parseVar <*> parseTypes) <*> parseCtorsH
  _ -> parseMr [] ts

-- Dist
parseDist :: ParseM Dist
parseDist = ParseM $ \ ts -> case ts of
  ((p, TkAmb) : ts) -> parseMr DistAmb ts
  ((p, TkFail) : ts) -> parseMr DistFail ts
  ((p, TkUni) : ts) -> parseMr DistUni ts
  ((p, _) : _) -> parseErr p ("expected one of " ++ show TkAmb ++ ", " ++ show TkFail ++ ", or " ++ show TkUni ++ " here")
  [] -> eofErr

-- List of Types
parseTypes :: ParseM [Type]
parseTypes = parseElse [] (parseType3 >>= \ tp -> fmap ((:) tp) parseTypes)

-- Program
parseProg :: ParseM UsProgs
parseProg = ParseM $ \ ts -> case ts of
-- define x : type = term; ...
  ((p, TkFun) : ts) -> parseMt ts $ pure UsProgFun <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkEq <*> parseTerm1 <* parseDrop TkSemicolon <*> parseProg
-- extern x : type; ...
  ((p, TkExtern) : ts) -> parseMt ts $ pure UsProgExtern <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkSemicolon <*> parseProg
-- data Y = ctors; ...
  ((p, TkData) : ts) -> parseMt ts $ pure UsProgData <*> parseVar <* parseDrop TkEq <*> parseCtors <* parseDrop TkSemicolon <*> parseProg
-- term
  _ -> parseMt ts $ pure UsProgExec <*> parseTerm1 <* parseDropSoft TkSemicolon

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
    else parseErr (fst (head ts')) "couldn't parse after this"

-- Parse a term
parseTerm :: String -> Either String UsTm
parseTerm s = lexStr s >>= parseOut parseTerm1

-- Parse a type
parseType :: String -> Either String Type
parseType s = lexStr s >>= parseOut parseType1

-- Parse a whole program.
parseFile :: String -> Either String UsProgs
parseFile s = lexStr s >>= parseOut parseProg
