module Parser where
import Exprs
import Lexer

newtype ParseM a = ParseM ([Token] -> Maybe (a, [Token]))

parseMf (ParseM f) = f
parseMt ts (ParseM f) = f ts
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

{-parseLams :: ParseM [Arg]
parseLams = ParseM $ \ ts -> case ts of
  (TkVar v : ts) -> parseMt ts $ pure ((:) . (,) v) <*> parseType1 <*>
    ParseM (\ ts -> case ts of
      (TkComma : ts) -> parseMt ts parseLams
      _ -> parseMr [] ts
    )

parseLamsAux :: FnQual -> UsTm -> ParseM UsTm
parseLamsAux fn tm = parseLams >>= \ (as, ts) -> parseMr (foldl (uncurry $ UsLam fn) tm as) ts-}

-- Previously part of parseTerm1
--  (TkLamAff : ts) -> parseMt ts $ pure (UsLam FnAff) <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseTerm1
--  (TkLamLin : ts) -> parseMt ts $ pure (UsLam FnLin) <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseTerm1
--  (TkLet : ts) -> parseMt ts $ pure UsLet <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkEq <*> parseTerm1 <* parseDrop TkIn <*> parseTerm1
--  (TkObserve : ts) -> parseMt ts $ pure UsObs <*> parseTerm1 <* parseDrop TkLeftArr <*> parseTerm1
--  (TkIf : ts) -> parseMt ts $ pure UsIf <*> parseTerm1 <* parseDrop TkThen <*> parseTerm1 <* parseDrop TkElse <*> parseTerm1

-- Previously part of parseTerm3
--  (TkFail : ts) -> parseMt ts $ pure UsFail <*> parseType
--  (TkAmb : ts) -> parseMt ts $ pure UsAmb <*> parseType
--  (TkUnit : ts) -> parseMr UsUnit ts
--  (TkTrue : ts) -> parseMr (UsBool True) ts
--  (TkFalse : ts) -> parseMr (UsBool False) ts
--  (TkInl : ts) -> parseMr (UsInj Inl) ts
--  (TkInr : ts) -> parseMr (UsInj Inr) ts

-- Lam, Let, Sample, Observe, If, Case
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

parseTermApp tm = ParseM $ \ ts ->
  maybe
    (parseMr tm ts)
    (uncurry $ parseMf . parseTermApp . UsApp tm)
    (parseMt ts parseTerm3)

-- Var, Fail, Unit, True, False, Inl, Inr, Parens
parseTerm3 :: ParseM UsTm
parseTerm3 = ParseM $ \ ts -> case ts of
  (TkVar v : ts) -> parseMr (UsVar v) ts
  (TkParenL : ts) -> parseMt ts $ parseTerm1 <* parseDrop TkParenR
  _ -> Nothing


parseType1 :: ParseM Type
parseType1 = ParseM $ \ ts -> parseMt ts parseType2 >>= \ (tp, ts) -> case ts of
  (TkArr : ts) -> parseMt ts $ pure (TpArr tp) <*> parseType1
  _ -> parseMr tp ts

parseType2 :: ParseM Type
parseType2 = parseType3
{-
parseType2 = ParseM $ \ ts -> parseMt ts parseType3 >>= \ (tp, ts') -> case ts' of
  (TkPlus : ts') -> parseMt ts' $ pure (TpSum tp) <*> parseType3
  _ -> parseMr tp ts'
-}

parseType3 :: ParseM Type
parseType3 = ParseM $ \ ts -> case ts of
  (TkVar v : ts) -> parseMr (TpVar v) ts
  (TkParenL : ts) -> parseMt ts $ parseType1 <* parseDrop TkParenR
  _ -> Nothing

--parseArgs :: ParseM [Arg]
--parseArgs = ParseM $ \ ts -> case ts of
--  (TkLam : ts) -> parseMt ts $ pure (\ v tp as -> (v, tp) : as) <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseArgs
--  (TkParenL : ts') -> parseMt ts' $ pure (:) <*> (pure (,) <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkParenR) <*> parseArgs
--  _ -> parseMr [] ts

parseCtors :: ParseM [Ctor]
parseCtors = ParseM $ \ ts -> case ts of
  (TkVar _ : _) -> parseMt (TkBar : ts) parseCtorsH
  _ -> parseMt ts parseCtorsH
parseCtorsH = ParseM $ \ ts -> case ts of
  (TkBar : ts) -> parseMt ts $ pure (:) <*> (pure Ctor <*> parseVar <*> parseTypes) <*> parseCtorsH
  _ -> parseMr [] ts



parseDist :: ParseM Dist
parseDist = ParseM $ \ ts -> case ts of
  (TkAmb : ts) -> parseMr DistAmb ts
  (TkFail : ts) -> parseMr DistFail ts
  (TkUni : ts) -> parseMr DistUni ts
  _ -> Nothing

parseTypes :: ParseM [Type]
parseTypes = ParseM $ \ ts ->
  maybe
    (parseMr [] ts)
    (\ (tp, ts) -> parseMt ts $ fmap ((:) tp) parseTypes)
    (parseMt ts parseType3)

parseProg :: ParseM UsProgs
parseProg = ParseM $ \ ts -> case ts of
-- fun f : type = term
  (TkFun : ts) -> parseMt ts $ pure UsProgFun <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkEq <*> parseTerm1 <*> parseProg
-- data T = ctors
  (TkData : ts) -> parseMt ts $ pure UsProgData <*> parseVar <* parseDrop TkEq <*> parseCtors <*> parseProg
-- exec term
  (TkExec : ts) -> parseMt ts $ pure UsProgExec <*> parseTerm1
  _ -> Nothing

parseOut :: ParseM a -> [Token] -> Maybe a
parseOut m ts = parseMf m ts >>= \ (a, ts') -> if length ts' == 0 then Just a else Nothing

parseTerm :: [Token] -> Maybe UsTm
parseTerm = parseOut parseTerm1

parseType :: [Token] -> Maybe Type
parseType = parseOut parseType1

-- Parse a whole program.
parseFile :: [Token] -> Maybe UsProgs
parseFile = parseOut parseProg
