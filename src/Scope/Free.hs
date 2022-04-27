{- Code for checking if a variable occurs affinely/linearly in a term -}
-- Note: this file has become pretty unfocused, and should probably get
-- moved in parts to other files at some point

module Scope.Free where
import Exprs
import Util.Helpers
import Scope.Subst
import qualified Data.Map as Map

-- For checking linearity, vars can appear:
-- LinNo: not at all
-- LinYes: just once
-- LinErr: multiple times
data Lin = LinNo | LinYes | LinErr
  deriving Eq

linIf :: Lin -> a -> a -> a -> a
linIf LinYes y n e = y
linIf LinNo  y n e = n
linIf LinErr y n e = e

linIf' :: Lin -> Lin -> Lin -> Lin
linIf' i y n = linIf i y n LinErr

-- Returns if x appears free in tm
isFree :: Var -> UsTm -> Bool
isFree x tm = Map.member x (freeVars tm)

-- Returns if x occurs at most once in tm
isAff :: Var -> UsTm -> Bool
isAff x tm = Map.findWithDefault 0 x (countOccs tm) <= 1
  where
    countOccs :: UsTm -> Map Var Int
    countOccs (UsVar x) = Map.singleton x 1
    countOccs (UsLam x tp tm) = Map.delete x $ countOccs tm
    countOccs (UsApp tm tm') = Map.unionWith (+) (countOccs tm) (countOccs tm')
    countOccs (UsCase tm cs) = foldr (Map.unionWith max . countOccsCase) (countOccs tm) cs
    countOccs (UsIf tm1 tm2 tm3) = Map.unionWith (+) (countOccs tm1) (Map.unionWith max (countOccs tm2) (countOccs tm3))
    countOccs (UsTmBool b) = Map.empty
    countOccs (UsSamp d tp) = Map.empty
    countOccs (UsLet x tp tm tm') = Map.unionWith max (countOccs tm) (Map.delete x $ countOccs tm')
    countOccs (UsAmb tms) = Map.unionsWith max (map countOccs tms)
--    countOccs (UsElimAmp tm o) = countOccs tm
    countOccs (UsProd am tms) = Map.unionsWith (if am == Additive then max else (+)) (map countOccs tms)
    countOccs (UsElimProd am tm xs tm') = Map.unionWith (+) (countOccs tm) (foldr Map.delete (countOccs tm') xs)
    countOccs (UsEqs tms) = Map.unionsWith (+) (map countOccs tms)
    
    countOccsCase :: CaseUs -> Map Var Int
    countOccsCase (CaseUs c xs tm) = foldr Map.delete (countOccs tm) xs

-- Returns if x appears exactly once in a user-term
isLin :: Var -> UsTm -> Bool
isLin x tm = h tm == LinYes where
  linCase :: CaseUs -> Lin
  linCase (CaseUs x' as tm') = if any ((==) x) as then LinNo else h tm'

  h_as dup = foldr (\ tm l -> linIf' l (linIf' (h tm) dup LinYes) (h tm)) LinNo
  
  h :: UsTm -> Lin
  h (UsVar x') = if x == x' then LinYes else LinNo
  h (UsLam x' tp tm) = if x == x' then LinNo else h tm
  h (UsApp tm tm') = h_as LinErr [tm, tm']
  h (UsCase tm []) = h tm
  h (UsCase tm cs) = linIf' (h tm)
    -- make sure x is not in any of the cases
    (foldr (\ c -> linIf' (linCase c) LinErr) LinYes cs)
    -- make sure x is linear in all the cases, or in none of the cases
    (foldr (\ c l -> if linCase c == l then l else LinErr) (linCase (head cs)) (tail cs))
  h (UsIf tm1 tm2 tm3) = linIf' (h tm1) (h_as LinErr [tm2, tm3]) (h_as LinYes [tm2, tm3])
  h (UsTmBool b) = LinNo
  h (UsSamp d tp) = LinNo
  h (UsLet x' tp tm tm') =
    if x == x' then h tm else h_as LinErr [tm, tm']
  h (UsAmb tms) = h_as LinYes tms
--  h (UsElimAmp tm o) = h tm
  h (UsProd am tms) = h_as (if am == Additive then LinYes else LinErr) tms
  h (UsElimProd am tm xs tm') = if x `elem` xs then h tm else h_as LinErr [tm, tm']
  h (UsEqs tms) = h_as LinErr tms

-- Returns if x appears exactly once in a term
isLin' :: Var -> Term -> Bool
isLin' x = (LinYes ==) . h where
  linCase :: Case -> Lin
  linCase (Case x' ps tm) = if any ((x ==) . fst) ps then LinNo else h tm

  h_as dup = foldr (\ tm l -> linIf' l (linIf' (h tm) dup LinYes) (h tm)) LinNo

  h :: Term -> Lin
  h (TmVarL x' tp) = if x == x' then LinYes else LinNo
  h (TmVarG gv x' tis as tp) = h_as LinErr (fsts as)
  h (TmLam x' tp tm tp') = if x == x' then LinNo else h tm
  h (TmApp tm1 tm2 tp2 tp) = h_as LinErr [tm1, tm2]
  h (TmLet x' xtm xtp tm tp) = if x == x' then h xtm else h_as LinErr [xtm, tm]
  h (TmCase tm y [] tp) = h tm
  h (TmCase tm y cs tp) = linIf' (h tm)
    -- make sure x is not in any of the cases
    (foldr (\ c -> linIf' (linCase c) LinErr) LinYes cs)
    -- make sure x is linear in all the cases, or in none of the cases
    (foldr (\ c l -> if linCase c == l then l else LinErr) (linCase (head cs)) (tail cs))
  h (TmSamp d tp) = LinNo
  h (TmAmb tms tp) = h_as LinYes tms
  h (TmProd am as) = h_as (if am == Additive then LinYes else LinErr) (fsts as)
--  h (TmElimAmp tm tps o) = h tm
  h (TmElimProd am tm ps tm' tp) =
    if x `elem` fsts ps then h tm else h_as LinErr [tm, tm']
  h (TmEqs tms) = h_as LinErr tms

-- Returns if a type has an arrow, ampersand, or recursive datatype anywhere in it
robust :: (Var -> Maybe [Ctor]) -> Type -> Bool
robust g = not . h [] where
  h :: [Var] -> Type -> Bool
  h visited (TpVar y as) = (y `elem` visited) || any (h (y : visited)) as || maybe False (any $ \ (Ctor _ tps) -> any (h (y : visited)) tps) (g y)
  h visited (TpArr _ _) = True
  h visited (TpProd am tps) = am == Additive || any (h visited) tps
  h visited NoTp = False

--------------------------------------------------

-- TODO: merge with isRecType code?
typeIsRecursive' :: (Var -> Maybe [Ctor]) -> Type -> Maybe [(Var, [Ctor])]
typeIsRecursive' g = h [] [] where
  anyM f = foldr ((|?|) . f) Nothing
  h visited datahist (TpVar y as) =
    (if y `elem` visited then Just datahist else Nothing)
      |?| anyM (h visited datahist) as
      |?| (g y >>= \ cs -> anyM (\ (Ctor _ tps) -> anyM (h (y : visited) ((y, cs) : datahist)) tps) cs)
  h visited datahist (TpArr tp1 tp2) = h visited datahist tp1 |?| h visited datahist tp2
  h visited datahist (TpProd am tps) = anyM (h visited datahist) tps
  h visited datahist NoTp = Nothing

-- Returns if a type has an infinite domain (i.e. it contains (mutually) recursive datatypes anywhere in it)
typeIsRecursive :: (Var -> Maybe [Ctor]) -> Type -> Bool
typeIsRecursive g = maybe False (const True) . typeIsRecursive' g

--------------------------------------------------

-- Returns if any of a list of types end up referencing a var
isRecType' :: Map Var [Ctor] -> Var -> [Type] -> Bool
isRecType' g y = h [] where
  h :: [Var] -> [Type] -> Bool
  h hist [] = False
  h hist (TpArr tp1 tp2 : tps) = h hist (tp1 : tp2 : tps)
  h hist (TpProd am tps' : tps) = h hist (tps' ++ tps)
  h hist (TpVar y' as : tps)
    | y == y' = True
    | y' `elem` hist = h hist tps
    | otherwise =
      maybe
        (h hist (as ++ tps))
        (\ cs -> h (y' : hist) (foldr (\ (Ctor x as') tps -> as' ++ tps) (as ++ tps) cs))
        (g Map.!? y')
  h hist (NoTp : tps) = h hist tps

-- Returns if y is a recursive datatype
isRecDatatype :: Map Var [Ctor] -> Var -> Bool
isRecDatatype g y =
  maybe False (isRecType' g y . concatMap (\ (Ctor _ tps) -> tps)) (g Map.!? y)

-- Returns if a type is a recursive datatype var
isRecType :: Map Var [Ctor] -> Type -> Bool
isRecType g (TpVar y _) = isRecDatatype g y
isRecType g _ = False

-- Returns the recursive datatypes in a file
getRecTypes' :: [(Var, [Var], [Var], [Ctor])] -> [Var]
getRecTypes' ds =
  let g = foldr (\ (y, tgs, xs, cs) -> Map.insert y cs) mempty ds in
    concat [if isRecDatatype g y then [y] else [] | (y, tgs, xs, cs) <- ds]

getDataSProgs :: [SProg] -> [(Var, [Var], [Var], [Ctor])]
getDataSProgs ps = concat [h p | p <- ps] where
  h (SProgData y tgs xs cs) = [(y, tgs, xs, cs)]
  h _ = []

getDataProgs :: [Prog] -> [(Var, [Var], [Var], [Ctor])]
getDataProgs ps = concat [h p | p <- ps] where
  h (ProgData y cs) = [(y, [], [], cs)]
  h _ = []

-- Returns the recursive datatypes in a file
getRecTypes :: Progs -> [Var]
getRecTypes (Progs ds end) = getRecTypes' (getDataProgs ds)

getRecTypesS :: SProgs -> [Var]
getRecTypesS (SProgs ds end) = getRecTypes' (getDataSProgs ds)
