module Parse where
import Exprs
import Lex

-- Parsing monad
newtype ParseM a = ParseM ([Token] -> Maybe (a, [Token]))

-- Extract the function from ParseM
parseMf (ParseM f) = f

-- Call a ParseM's function with some tokens
parseMt ts (ParseM f) = f ts

-- Given something and a list of tokens, return them in the ParseM monad
parseMr = curry Just

-- Consume token t.
parseDrop t = ParseM $ \ ts -> case ts of
  (t' : ts') -> if t == t' then parseMr () ts' else Nothing
  _ -> Nothing

-- Consume token t if there is one.
parseDropSoft t = ParseM $ \ ts -> case ts of
  (t' : ts') -> parseMr () (if t == t' then ts' else ts)
  _ -> parseMr () ts

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

-- Parse a symbol.
parseVar :: ParseM Var
parseVar = ParseM $ \ ts -> case ts of
  (TkVar v : ts) -> parseMr v ts
  _ -> Nothing

-- Parse zero or more symbols.
parseVars :: ParseM [Var]
parseVars = ParseM $ \ ts -> case ts of
  (TkVar v : ts) -> parseMt ts $ pure ((:) v) <*> parseVars
  _ -> parseMr [] ts

-- Parse a branch of a case expression.
parseCase :: ParseM CaseUs
parseCase = ParseM $ \ ts -> case ts of
  (TkBar : ts) -> parseMt ts parseCase
  (TkVar c : ts) -> parseMt ts $ pure (CaseUs c) <*> parseVars <* parseDrop TkArr <*> parseTerm1

-- Parse zero or more branches of a case expression.
parseCases :: ParseM [CaseUs]
parseCases = (*>) (parseDropSoft TkBar) $ ParseM $ \ ts -> case ts of
  (TkVar _ : _) -> parseMt ts $ pure (:) <*> parseCase <*> parseCases
  _ -> parseMr [] ts

-- Lam, Sample, CaseOf
parseTerm1 :: ParseM UsTm
parseTerm1 = ParseM $ \ ts -> case ts of
-- \ x : type -> term
  (TkLam : ts) -> parseMt ts $ pure UsLam <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseTerm1
-- sample dist x
  (TkSample : ts) -> parseMt ts $ pure UsSamp <*> parseDist <*> parseVar
-- case term of cases
  (TkCase : ts) -> parseMt ts $ pure UsCase <*> parseTerm1 <* parseDrop TkOf <*> parseCases
  _ -> parseMt ts parseTerm2

-- App
parseTerm2 :: ParseM UsTm
parseTerm2 = ParseM $ \ ts -> parseMt ts parseTerm3 >>= uncurry (parseMf . parseTermApp)

-- Parse an application spine
parseTermApp tm = ParseM $ \ ts ->
  maybe
    (parseMr tm ts)
    (uncurry $ parseMf . parseTermApp . UsApp tm)
    (parseMt ts parseTerm3)

-- Var, Parens
parseTerm3 :: ParseM UsTm
parseTerm3 = ParseM $ \ ts -> case ts of
  (TkVar v : ts) -> parseMr (UsVar v) ts
  (TkParenL : ts) -> parseMt ts $ parseTerm1 <* parseDrop TkParenR
  _ -> Nothing


-- Arrow
parseType1 :: ParseM Type
parseType1 = ParseM $ \ ts -> parseMt ts parseType2 >>= \ (tp, ts) -> case ts of
  (TkArr : ts) -> parseMt ts $ pure (TpArr tp) <*> parseType1
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
  (TkVar v : ts) -> parseMr (TpVar v) ts
  (TkParenL : ts) -> parseMt ts $ parseType1 <* parseDrop TkParenR
  _ -> Nothing

-- List of Constructors
parseCtors :: ParseM [Ctor]
parseCtors = ParseM $ \ ts -> case ts of
  (TkVar _ : _) -> parseMt (TkBar : ts) parseCtorsH
  _ -> parseMt ts parseCtorsH
parseCtorsH = ParseM $ \ ts -> case ts of
  (TkBar : ts) -> parseMt ts $ pure (:) <*> (pure Ctor <*> parseVar <*> parseTypes) <*> parseCtorsH
  _ -> parseMr [] ts

-- Dist
parseDist :: ParseM Dist
parseDist = ParseM $ \ ts -> case ts of
  (TkAmb : ts) -> parseMr DistAmb ts
  (TkFail : ts) -> parseMr DistFail ts
  (TkUni : ts) -> parseMr DistUni ts
  _ -> Nothing

-- List of Types
parseTypes :: ParseM [Type]
parseTypes = ParseM $ \ ts ->
  maybe
    (parseMr [] ts)
    (\ (tp, ts) -> parseMt ts $ fmap ((:) tp) parseTypes)
    (parseMt ts parseType3)

-- Program
parseProg :: ParseM UsProgs
parseProg = ParseM $ \ ts -> case ts of
-- define f : type = term; ...
  (TkFun : ts) -> parseMt ts $ pure UsProgFun <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkEq <*> parseTerm1 <* parseDrop TkSemicolon <*> parseProg
-- extern f : type; ...
  (TkExtern : ts) -> parseMt ts $ pure UsProgExtern <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkSemicolon <*> parseProg
-- data T = ctors; ...
  (TkData : ts) -> parseMt ts $ pure UsProgData <*> parseVar <* parseDrop TkEq <*> parseCtors <* parseDrop TkSemicolon <*> parseProg
-- term
  _ -> parseMt ts $ pure UsProgExec <*> parseTerm1
--  (TkExec : ts) -> parseMt ts $ pure UsProgExec <*> parseTerm1
--  _ -> Nothing

-- Extract the value from a ParseM, if it consumed all tokens
parseOut :: ParseM a -> [Token] -> Maybe a
parseOut m ts = parseMf m ts >>= \ (a, ts') -> if length ts' == 0 then Just a else Nothing

-- Parse a term
parseTerm :: [Token] -> Maybe UsTm
parseTerm = parseOut parseTerm1

-- Parse a type
parseType :: [Token] -> Maybe Type
parseType = parseOut parseType1

-- Parse a whole program.
parseFile :: [Token] -> Maybe UsProgs
parseFile = parseOut parseProg
