module Parser where
import Exprs
import Lexer

newtype ParseM a = ParseM ([Token] -> Maybe (a, [Token]))

parseMf (ParseM f) = f
parseMt ts (ParseM f) = f ts
parseMr = curry Just

parseDrop t = ParseM $ \ ts -> case ts of
  (t' : ts') -> if t == t' then parseMr () ts' else Nothing
  _ -> Nothing

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


parseVar = ParseM $ \ ts -> case ts of
  (TkVar v : ts) -> parseMr v ts
  _ -> Nothing

parseVars = ParseM $ \ ts -> case ts of
  (TkVar v : ts) -> parseMt ts $ pure ((:) v) <*> parseVars
  _ -> parseMr [] ts

parseCase = ParseM $ \ ts -> case ts of
  (TkBar : ts) -> parseMt ts parseCase
  (TkVar c : ts) -> parseMt ts $ pure (Case c) <*> parseVars <* parseDrop TkArr <*> parseTerm1

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

parseLamsAux :: FnQual -> Term -> ParseM Term
parseLamsAux fn tm = parseLams >>= \ (as, ts) -> parseMr (foldl (uncurry $ TmLam fn) tm as) ts-}

-- Lam, Let, Sample, Observe, If, Case
parseTerm1 = ParseM $ \ ts -> case ts of
--  (TkLam : ts) -> parseMt ts $ pure (TmLam FnUnr) <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseTerm1
  (TkLamAff : ts) -> parseMt ts $ pure (TmLam FnAff) <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseTerm1
  (TkLamLin : ts) -> parseMt ts $ pure (TmLam FnLin) <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseTerm1
--  (TkLet : ts) -> parseMt ts $ pure TmLet <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkEq <*> parseTerm1 <* parseDrop TkIn <*> parseTerm1
  (TkSample : ts) -> parseMt ts $ pure TmSamp <*> parseTerm1
  (TkObserve : ts) -> parseMt ts $ pure TmObs <*> parseTerm1 <* parseDrop TkLeftArr <*> parseTerm1
--  (TkIf : ts) -> parseMt ts $ pure TmIf <*> parseTerm1 <* parseDrop TkThen <*> parseTerm1 <* parseDrop TkElse <*> parseTerm1
  (TkCase : ts) -> parseMt ts $ pure TmCase <*> parseTerm1 <* parseDrop TkOf <*> parseCases
  _ -> parseMt ts parseTerm2

-- App
parseTerm2 = ParseM $ \ ts -> parseMt ts parseTerm3 >>= uncurry (parseMf . parseTermApp)

parseTermApp tm = ParseM $ \ ts ->
  maybe
    (parseMr tm ts)
    (uncurry $ parseMf . parseTermApp . TmApp tm)
    (parseMt ts parseTerm3)

-- Var, Fail, Unit, True, False, Inl, Inr, Parens
parseTerm3 = ParseM $ \ ts -> case ts of
  (TkVar v : ts) -> parseMr (TmVar v) ts
  (TkFail : ts) -> parseMr TmFail ts
--  (TkUnit : ts) -> parseMr TmUnit ts
--  (TkTrue : ts) -> parseMr (TmBool True) ts
--  (TkFalse : ts) -> parseMr (TmBool False) ts
--  (TkInl : ts) -> parseMr (TmInj Inl) ts
--  (TkInr : ts) -> parseMr (TmInj Inr) ts
  (TkParenL : ts) -> parseMt ts $ parseTerm1 <* parseDrop TkParenR
  _ -> Nothing


--parseType1 :: ParseM Type
parseType1 = ParseM $ \ ts -> parseMt ts parseType2 >>= \ (tp, ts) -> case ts of
  (TkArr    : ts) -> parseMt ts $ pure (TpArr tp FnUnr) <*> parseType1
  (TkArrAff : ts) -> parseMt ts $ pure (TpArr tp FnAff) <*> parseType1
  (TkArrLin : ts) -> parseMt ts $ pure (TpArr tp FnLin) <*> parseType1
  _ -> parseMr tp ts

--parseType2 :: ParseM Type
parseType2 = parseType3
{-
parseType2 = ParseM $ \ ts -> parseMt ts parseType3 >>= \ (tp, ts') -> case ts' of
  (TkPlus : ts') -> parseMt ts' $ pure (TpSum tp) <*> parseType3
  _ -> parseMr tp ts'
-}

--parseType3 :: ParseM Type
parseType3 = ParseM $ \ ts -> case ts of
--  (TkUnit : ts) -> parseMr TpUnit ts
--  (TkBool : ts) -> parseMr TpBool ts
  (TkVar v : ts) -> parseMr (TpVar v) ts
  (TkParenL : ts) -> parseMt ts $ parseType1 <* parseDrop TkParenR
  _ -> Nothing

parseArgs = ParseM $ \ ts -> case ts of
  (TkLam : ts) -> parseMt ts $ pure (\ v tp as -> (v, tp) : as) <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseArgs
--  (TkParenL : ts') -> parseMt ts' $ pure (:) <*> (pure (,) <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkParenR) <*> parseArgs
  _ -> parseMr [] ts
parseCtors = ParseM $ \ ts -> case ts of
  (TkVar _ : _) -> parseMt (TkBar : ts) parseCtorsH
  _ -> parseMt ts parseCtorsH
parseCtorsH = ParseM $ \ ts -> case ts of
  (TkBar : ts) -> parseMt ts $ pure (:) <*> (pure Ctor <*> parseVar <*> parseTypes) <*> parseCtorsH
  _ -> parseMr [] ts

parseTypes = ParseM $ \ ts ->
  maybe
    (parseMr [] ts)
    (\ (tp, ts) -> parseMt ts $ fmap ((:) tp) parseTypes)
    (parseMt ts parseType3)

parseProg :: ParseM Progs
parseProg = ParseM $ \ ts -> case ts of
  (TkFun : ts) -> parseMt ts $ pure ProgFun <*> parseVar <* parseDrop TkEq <*> parseArgs <*> parseTerm1 <*> parseProg
  (TkData : ts) -> parseMt ts $ pure ProgData <*> parseVar <* parseDrop TkEq <*> parseCtors <*> parseProg
  (TkRun : ts) -> parseMt ts $ pure ProgRun <*> parseTerm1
  _ -> Nothing

--parseOut :: ParseM a -> [Token] -> Maybe a
parseOut m ts = parseMf m ts >>= \ (a, ts') -> if length ts' == 0 then Just a else Nothing

parseTerm = parseOut parseTerm1
parseType = parseOut parseType1
parseFile = parseOut parseProg
