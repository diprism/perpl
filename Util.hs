module Util where
import Exprs


maybe2 :: Maybe a -> b -> (a -> b) -> b
maybe2 m n j = maybe n j m

okay :: Monad m => m ()
okay = return ()

plus_l :: Num a => a -> [a] -> [a]
a `plus_l` as = map ((+) a) as

combine :: [[a]] -> ([a], [[Int]])
combine as =
  (concat as,
   foldr (\ as' is i -> [i..i + length as' - 1] : is (i + length as'))
     (const []) as 0)



dropFromEnd :: Int -> [a] -> [a]
dropFromEnd i as = take (length as - i) as

splitArrows :: Type -> [Type]
splitArrows (TpArr tp1 tp2) = splitArrows tp1 ++ [tp2]
splitArrows (TpVar y) = [TpVar y]

joinArrows :: [Type] -> Type
joinArrows [] = error "joinArrows on []"
joinArrows [tp] = tp
joinArrows (tp : tps) = TpArr tp $ joinArrows tps

splitAppsh :: Term -> Type -> ((Term, Type), [(Term, Type)])
splitAppsh (TmApp tm1 tm2 tp2 tp) tp' =
  let (hd, as) = splitAppsh tm1 tp in
    (hd, as ++ [(tm2, tp2)])
splitAppsh tm tp = ((tm, tp), [])

splitApps :: Term -> ((Term, Type), [(Term, Type)])
splitApps tm = splitAppsh tm (error "splitApps expects a TmApp")

ctorEtaName :: Var -> Int -> Var
ctorEtaName x i = show i ++ x

ctorEtaExpand :: Var -> Type -> Term
ctorEtaExpand x tp =
  let tps' = splitArrows tp
      tps = dropFromEnd 1 tps'
      etas = map (ctorEtaName x) [0..length tps - 1]
--      (atm, [end]) = foldl (\ (tm, (atp : tps)) a -> (TmApp tm (TmVar a atp ScopeLocal) atp (joinArrows tps), tps)) (TmVar x tp ScopeCtor, tps') etas in
      atm = TmCtor x (zip etas tps) in
    foldr (\ a f (atp : tps) -> TmLam a atp (f tps) (joinArrows tps))
      (const atm) etas tps'
