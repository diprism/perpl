module Util where
import Exprs

-- Creates a matrix of all possible combinations of two lists
kronecker :: [a] -> [b] -> [[(a, b)]]
kronecker as bs = map (\ a -> map (\ b -> (a, b)) bs) as

weightsRow :: Num n => Int {- Index -} -> Int {- Length -} -> [n]
weightsRow i l = map (\ j -> if j == i then 1 else 0) [0..l-1]

-- Argument-reordered version of maybe
maybe2 :: Maybe a -> b -> (a -> b) -> b
maybe2 m n j = maybe n j m

okay :: Monad m => m ()
okay = return ()

plus_l :: Num a => a -> [a] -> [a]
a `plus_l` as = map ((+) a) as

-- Concatenates a list of lists, returning that and a
-- list mapping original positions to their new indices
-- within the concatenated list
combine :: [[a]] -> ([a], [[Int]])
combine as =
  (concat as,
   foldr (\ as' is i -> [i..i + length as' - 1] : is (i + length as'))
     (const []) as 0)


-- Gets the type of an elaborated term in O(1) time
getType :: Term -> Type
getType (TmVar x tp sc) = tp
getType (TmLam x tp tm tp') = TpArr tp tp'
getType (TmApp tm1 tm2 tp2 tp) = tp
getType (TmCase tm cs y tp) = tp
getType (TmSamp d y) = TpVar y

-- Extracts the start term at the end of a program
getStartTerm :: Progs -> Term
getStartTerm (ProgExec tm) = tm
getStartTerm (ProgFun x tp tm ps) = getStartTerm ps
getStartTerm (ProgData y cs ps) = getStartTerm ps

-- Splits tp1 -> tp2 -> ... -> tpn into ([tp1, tp2, ...], tpn)
splitArrows :: Type -> ([Type], Type)
splitArrows (TpArr tp1 tp2) = let (tps, end) = splitArrows tp2 in (tp1 : tps, end)
splitArrows tp = ([], tp)

-- Joins ([tp1, tp2, ...], tpn) into tp1 -> tp2 -> ... -> tpn
joinArrows :: [Type] -> Type -> Type
joinArrows tps end = foldr TpArr end tps

-- Splits a series of TmApps into the head term and its args
splitApps :: Term -> ((Term, Type), [(Term, Type)])
splitApps tm = splitAppsh tm (error "splitApps expects a TmApp")
  where
    splitAppsh :: Term -> Type -> ((Term, Type), [(Term, Type)])
    splitAppsh (TmApp tm1 tm2 tp2 tp) tp' =
      let (hd, as) = splitAppsh tm1 tp in
        (hd, as ++ [(tm2, tp2)])
    splitAppsh tm tp = ((tm, tp), [])
