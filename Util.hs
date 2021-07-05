module Util where
import Exprs

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f (Left a) = Left (f a)
mapLeft f (Right c) = Right c

-- Creates a matrix of all possible combinations of two lists
kronecker :: [a] -> [b] -> [[(a, b)]]
kronecker as bs = map (\ a -> map (\ b -> (a, b)) bs) as

kronwith :: (a -> b -> c) -> [a] -> [b] -> [c]
kronwith f as bs = map (uncurry f) $ concat $ kronecker as bs

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
getType (TmCtor x as y) = TpVar y

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

joinApps :: Term -> [(Term, Type)] -> Type -> Term
joinApps tm as end =
  let tps = foldr (\ (_, atp) (atp' : atps) -> TpArr atp atp' : atp' : atps) [end] as in
    h tm as (tail tps)
  where
  h :: Term -> [(Term, Type)] -> [Type] -> Term
  h tm [] [] = tm
  h tm ((a, atp) : as) (tp : tps) = h (TmApp tm a atp tp) as tps

splitUsApps :: UsTm -> (UsTm, [UsTm])
splitUsApps = h [] where
  h as (UsApp tm1 tm2) = h (tm2 : as) tm1
  h as tm = (tm, as)

addLams :: Term -> [(Var, Type)] -> Term
addLams tm = fst  . foldr
  (\ (a, atp) (tm, tp) ->
    (TmLam a atp tm tp, TpArr atp tp))
  (tm, getType tm)


toTermArgs :: [(Var, Type)] -> [(Term, Type)]
toTermArgs = map $ \ (a, atp) -> (TmVar a atp ScopeLocal, atp)

-- Naming convention for testing equality two terms of the same type
typeFactorName :: Type -> String
typeFactorName tp = "==" ++ show tp

-- Naming convention for factor v=(v1,v2)
pairFactorName :: Type -> Type -> String
pairFactorName tp1 tp2 = "v=(" ++ show (TpArr tp1 tp2) ++ ")"

-- Naming convention for constructor factor
ctorFactorName :: Var -> [(Term, Type)] -> String
ctorFactorName x as = "v=" ++ show (TmCtor x as "irrelevant")

-- Establishes naming convention for eta-expanding a constructor.
-- So Cons h t -> (\ ?Cons0. \ ?Cons1. Cons ?Cons0 ?Cons1) h t.
-- This is necessary so that the FGG can use one rule for each
-- constructor, and not for each usage of it in the code.
-- It also fixes the issue of partially-applied constructors.
ctorEtaName :: Var -> Int -> Var
ctorEtaName x i = "?" ++ x ++ show i


-- Returns the names of the args for a constructor
ctorGetArgs :: Var -> [Type] -> [(Var, Type)]
ctorGetArgs x tps =
  zip (map (ctorEtaName x) [0..length tps - 1]) tps

-- Turns a constructor into one with all its args applied
ctorAddArgs :: Var -> [(Term, Type)] -> [(Var, Type)] -> Var -> Term
ctorAddArgs x tas vas y =
  TmCtor x (tas ++ map (\ (a, atp) -> (TmVar a atp ScopeLocal, atp)) vas) y

-- Eta-expands a constructor with the necessary extra args
ctorEtaExpand :: Var -> [(Term, Type)] -> [(Var, Type)] -> Var -> Term
ctorEtaExpand x tas vas y =
  foldr (\ (a, atp) tm -> TmLam a atp tm (getType tm))
    (ctorAddArgs x tas vas y) vas

ctorDefault :: Var -> [Type] -> Var -> Term
ctorDefault x as y = TmCtor x (map (\ (a, atp) -> (TmVar a atp ScopeLocal, atp)) (ctorGetArgs x as)) y
