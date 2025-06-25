{- Code for checking if a variable occurs affinely/linearly in a term -}
-- Note: this file has become pretty unfocused, and should probably get
-- moved in parts to other files at some point

module Scope.Free where
import Struct.Lib
import Util.Helpers
import Scope.Subst (Subst(tags, tpVars), subst)
import Scope.Ctxt (Ctxt(tpNames), ctxtLookupType2)
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

-- Returns if x occurs at most once in tm
isAff :: TmVar -> UsTm -> Bool
isAff x tm = Map.findWithDefault 0 x (countOccs tm) <= 1
  where
    countOccs :: UsTm -> Map TmVar Int
    countOccs (UsVar x) = Map.singleton x 1
    countOccs (UsLam x tp tm) = Map.delete x $ countOccs tm
    countOccs (UsApp tm tm') = Map.unionWith (+) (countOccs tm) (countOccs tm')
    countOccs (UsCase tm cs) = foldr (Map.unionWith max . countOccsCase) (countOccs tm) cs
    countOccs (UsIf tm1 tm2 tm3) = Map.unionWith (+) (countOccs tm1) (Map.unionWith max (countOccs tm2) (countOccs tm3))
    countOccs (UsTmBool b) = Map.empty
    countOccs (UsLet x tm tm') = Map.unionWith (+) (countOccs tm) (Map.delete x $ countOccs tm')
    countOccs (UsAmb tms) = Map.unionsWith max (map countOccs tms)
    countOccs (UsFactorDouble wt tm) = countOccs tm
    countOccs (UsFactorNat wt tm) = countOccs tm
    countOccs (UsFactorRatio wt tm) = countOccs tm
    countOccs (UsFail tp) = Map.empty
--    countOccs (UsElimAmp tm o) = countOccs tm
    countOccs (UsProd am tms) = Map.unionsWith (if am == Additive then max else (+)) (map countOccs tms)
    countOccs (UsElimMultiplicative tm xs tm') = Map.unionWith (+) (countOccs tm) (foldr Map.delete (countOccs tm') xs)
    countOccs (UsElimAdditive tm n i x tm') = Map.unionWith (+) (countOccs tm) (Map.delete x (countOccs tm'))
    countOccs (UsEqs tms) = Map.unionsWith (+) (map countOccs tms)
    
    countOccsCase :: CaseUs -> Map TmVar Int
    countOccsCase (CaseUs c xs tm) = foldr Map.delete (countOccs tm) xs

-- Returns if x appears exactly once in a term
isLin :: TmVar -> Term -> Bool
isLin x = (LinYes ==) . h where
  linCase :: Case -> Lin
  linCase (Case x' ps tm) = if any ((x ==) . fst) ps then LinNo else h tm

  h_as dup = foldr (\ tm l -> linIf' l (linIf' (h tm) dup LinYes) (h tm)) LinNo

  h :: Term -> Lin
  h (TmVarL x' tp) = if x == x' then LinYes else LinNo
  h (TmVarG gv x' tgs tis as tp) = h_as LinErr (fsts as)
  h (TmLam x' tp tm tp') = if x == x' then LinNo else h tm
  h (TmApp tm1 tm2 tp2 tp) = h_as LinErr [tm1, tm2]
  h (TmLet x' xtm xtp tm tp) = if x == x' then h xtm else h_as LinErr [xtm, tm]
  h (TmCase tm y [] tp) = h tm
  h (TmCase tm y cs tp) = linIf' (h tm)
    -- make sure x is not in any of the cases
    (foldr (\ c -> linIf' (linCase c) LinErr) LinYes cs)
    -- make sure x is linear in all the cases, or in none of the cases
    (foldr (\ c l -> if linCase c == l then l else LinErr) (linCase (head cs)) (tail cs))
  h (TmAmb tms tp) = h_as LinYes tms
  h (TmFactorDouble wt tm tp) = h tm
  h (TmFactorNat wt tm tp) = h tm
  h (TmFactorRatio wt tm tp) = h tm
  h (TmProd am as) = h_as (if am == Additive then LinYes else LinErr) (fsts as)
  h (TmElimAdditive tm n i p tm' tp) =
    if x == fst p then h tm else h_as LinErr [tm, tm']
  h (TmElimMultiplicative tm ps tm' tp) =
    if x `elem` fsts ps then h tm else h_as LinErr [tm, tm']
  h (TmEqs tms) = h_as LinErr tms


{- searchType g pred tp

Search through type tp's tree, looking for a node for which pred is true.
g maps a datatype name to its list of constructors, if any.
pred takes two arguments, a list of visited nodes and a node.
-}

searchType :: ([Type] -> Type -> Bool) -> Ctxt -> Type -> Bool
searchType pred g = h [] where
  h :: [Type] -> Type -> Bool
  h visited tp = pred visited tp || case tp of
    TpData y tgs as ->
      -- Don't search the same type twice (that would cause infinite recursion)
      not (tp `elem` visited) &&
      case ctxtLookupType2 g y of
        Nothing -> False
        Just (tgs', ps, cs) ->
          -- Substitute actual type parameters for datatype's type parameters
          -- and recurse on each constructor
          let s = mempty{tags   = Map.fromList (pickyZip tgs' tgs),
                         tpVars = Map.fromList (pickyZip ps   as )} in
          any (\ (Ctor _ tps) -> any (h (tp : visited) . subst s) tps) cs
    TpArr tp1 tp2 -> h visited tp1 || h visited tp2
    TpProd am tps -> any (h visited) tps
    _ -> False

-- Returns if a type has no arrow, ampersand, or recursive datatype anywhere in it
robust :: Ctxt -> Type -> Bool
robust g tp = not (searchType p g tp) where
  p visited tp@(TpData y tgs as) = tp `elem` visited
  p visited (TpArr _ _) = True
  p visited (TpProd Additive _) = True
  p visited _ = False

-- Returns if a type has no arrow or ampersand types anywhere in it
positive :: Ctxt -> Type -> Bool
positive g tp = not (searchType p g tp) where
  p visited (TpArr _ _) = True
  p visited (TpProd Additive _) = True
  p visited _ = False


-- Returns if a type has an infinite domain (i.e. it contains (mutually) recursive datatypes anywhere in it)
isInfiniteType :: Ctxt -> Type -> Bool
isInfiniteType = searchType p where
  p visited tp@(TpData y tgs as) = tp `elem` visited
  p _ _ = False

-- Returns if a type is a (mutually) recursive datatype
isRecursiveType :: Ctxt -> Type -> Bool
isRecursiveType g tp = searchType p g tp where
  p visited tp'@(TpData y tgs as) = tp' `elem` visited && tp' == tp
  p _ _ = False

isRecursiveTypeName :: Ctxt -> TpName -> Bool
isRecursiveTypeName g y =
  isRecursiveType g (TpData y [] []) -- this function currently used only after monomorphization, so empty type parameter list okay

-- Returns the recursive datatypes in a file
getRecursiveTypeNames :: Ctxt -> [TpName]
getRecursiveTypeNames g = filter (isRecursiveTypeName g) (Map.keys (tpNames g))
