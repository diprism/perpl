module Free where
import Exprs
import Ctxt
import Util
import qualified Data.Map as Map
import Data.List
import Data.Char

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


-- Returns a map of the free vars in a term, with the max number of occurrences
freeVars :: UsTm -> Map.Map Var Int
freeVars (UsVar x) = Map.singleton x 1
freeVars (UsLam x tp tm) = Map.delete x $ freeVars tm
freeVars (UsApp tm tm') = Map.unionWith (+) (freeVars tm) (freeVars tm')
freeVars (UsCase tm cs) = foldr (Map.unionWith max . freeVarsCase) (freeVars tm) cs
freeVars (UsSamp d tp) = Map.empty
freeVars (UsLet x tm tm') = Map.unionWith max (freeVars tm) (Map.delete x $ freeVars tm')
freeVars (UsAmb tms) = Map.unionsWith max (map freeVars tms)
freeVars (UsAmpIn tms) = Map.unionsWith max (map freeVars tms)
freeVars (UsAmpOut tm o) = freeVars tm
freeVars (UsProdIn tms) = Map.unionsWith (+) (map freeVars tms)
freeVars (UsProdOut tm xs tm') = Map.unionWith (+) (freeVars tm) (foldr Map.delete (freeVars tm') xs)

freeVarsCase :: CaseUs -> Map.Map Var Int
freeVarsCase (CaseUs c xs tm) = foldr Map.delete (freeVars tm) xs


-- Returns the local vars that occur free in a term, along with their types
type FreeVars = Map.Map Var Type

freeVars' :: Term -> FreeVars
freeVars' (TmVarL x tp) = Map.singleton x tp
freeVars' (TmVarG gv x as tp) = freeVarsArgs' as
freeVars' (TmLam x tp tm tp') = Map.delete x $ freeVars' tm
freeVars' (TmApp tm1 tm2 tp2 tp) = Map.union (freeVars' tm1) (freeVars' tm2)
freeVars' (TmLet x xtm xtp tm tp) = Map.union (freeVars' xtm) (Map.delete x (freeVars' tm))
freeVars' (TmCase tm y cs tp') = Map.union (freeVars' tm) (freeVarsCases' cs)
freeVars' (TmSamp d tp) = Map.empty
freeVars' (TmAmb tms tp) = Map.unions (map freeVars' tms)
freeVars' (TmAmpIn as) = freeVarsArgs' as
freeVars' (TmAmpOut tm tps o) = freeVars' tm
freeVars' (TmProdIn as) = freeVarsArgs' as
freeVars' (TmProdOut tm ps tm' tp) = Map.union (freeVars' tm) (foldr (Map.delete . fst) (freeVars' tm') ps)

freeVarsCase' :: Case -> FreeVars
freeVarsCase' (Case c as tm) = foldr (Map.delete . fst) (freeVars' tm) as

freeVarsCases' :: [Case] -> FreeVars
freeVarsCases' = Map.unions . map (freeVarsCase')

freeVarsArgs' :: [Arg] -> FreeVars
freeVarsArgs' = Map.unions . map (freeVars' . fst)


-- Returns the (max) number of occurrences of x in tm
freeOccurrences :: Var -> UsTm -> Int
freeOccurrences x tm = Map.findWithDefault 0 x (freeVars tm)

-- Returns if x appears free in tm
isFree :: Var -> UsTm -> Bool
isFree x tm = Map.member x (freeVars tm)

-- Returns if x occurs at most once in tm
isAff :: Var -> UsTm -> Bool
isAff x tm = freeOccurrences x tm <= 1

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
  h (UsSamp d tp) = LinNo
  h (UsLet x' tm tm') =
    if x == x' then h tm else h_as LinErr [tm, tm']
  h (UsAmb tms) = h_as LinYes tms
  h (UsAmpIn tms) = h_as LinYes tms
  h (UsAmpOut tm o) = h tm
  h (UsProdIn tms) = h_as LinErr tms
  h (UsProdOut tm xs tm') = if x `elem` xs then h tm else h_as LinErr [tm, tm']

-- Returns if x appears exactly once in a term
isLin' :: Var -> Term -> Bool
isLin' x = (LinYes ==) . h where
  linCase :: Case -> Lin
  linCase (Case x' ps tm) = if any ((x ==) . fst) ps then LinNo else h tm

  h_as dup = foldr (\ tm l -> linIf' l (linIf' (h tm) dup LinYes) (h tm)) LinNo

  h :: Term -> Lin
  h (TmVarL x' tp) = if x == x' then LinYes else LinNo
  h (TmVarG gv x' as tp) = h_as LinErr (map fst as)
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
  h (TmAmpIn as) = h_as LinYes (map fst as)
  h (TmAmpOut tm tps o) = h tm
  h (TmProdIn as) = h_as LinErr (map fst as)
  h (TmProdOut tm ps tm' tp) =
    if x `elem` map fst ps then h tm else h_as LinErr [tm, tm']

-- Returns if a type has an infinite domain (i.e. it contains (mutually) recursive datatypes anywhere in it)
typeIsRecursive :: Ctxt -> Type -> Bool
typeIsRecursive g = h [] where
  h visited (TpVar y) =
    y `elem` visited ||
      maybe False
        (any $ \ (Ctor _ tps) -> any (h (y : visited)) tps)
        (ctxtLookupType g y)
  h visited (TpArr tp1 tp2) = h visited tp1 || h visited tp2
  h visited (TpAmp tps) = any (h visited) tps
  h visited (TpProd tps) = any (h visited) tps

-- Returns if a type has an arrow, ampersand, or recursive datatype anywhere in it
useOnlyOnce :: Ctxt -> Type -> Bool
useOnlyOnce g = h [] where
  h visited (TpVar y) = (y `elem` visited) || maybe False (any $ \ (Ctor _ tps) -> any (h (y : visited)) tps) (ctxtLookupType g y)
  h visited (TpArr _ _) = True
  h visited (TpAmp tps) = True
  h visited (TpProd tps) = any (h visited) tps
