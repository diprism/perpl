module Compile where
import Data.List
import Exprs
import FGG
import Check

data RuleM x = RuleM [Rule] [(Var, Type)] x

instance Functor RuleM where
  fmap a2b (RuleM rs xs a) = RuleM rs xs (a2b a)
instance Applicative RuleM where
  pure a = RuleM [] [] a
  RuleM rs xs a2b <*> RuleM rs' xs' a = RuleM (rs ++ rs') (xs ++ xs') (a2b a)
instance Monad RuleM where
  RuleM rs xs a >>= a2mb =
    let (RuleM rs' xs' b) = a2mb a in
      RuleM (rs ++ rs') (xs ++ xs') b

addExts :: [(Var, Type)] -> RuleM ()
addExts xs = RuleM [] xs ()

addExt :: Var -> Type -> RuleM ()
addExt x tp = addExts [(x, tp)]

addRules :: [Rule] -> RuleM ()
addRules rs = RuleM rs [] ()

addRule :: Rule -> RuleM ()
addRule r = addRules [r]

addRule' :: String -> [Type] -> [Edge] -> [Int] -> RuleM ()
addRule' lhs ns es xs = addRule $ Rule lhs $ HGF (map show ns) es xs

-- Local var rule
var2fgg :: Var -> Type -> RuleM ()
var2fgg x tp =
  addRule' x [tp, tp] [Edge [0, 1] ("=" ++ show tp)] [0, 1]

getExts :: RuleM a -> RuleM [(Var, Type)]
getExts (RuleM rs xs a) = RuleM rs xs xs

getRules :: RuleM a -> [Rule]
getRules (RuleM rs xs a) = rs

bindExts :: [(Var, Type)] -> RuleM a -> RuleM a
bindExts xs' (RuleM rs xs a) =
  let keep = flip elem (map fst xs') . fst in
  sequence (map (uncurry var2fgg) xs') >> RuleM rs (filter keep xs) a

bindExt :: Var -> Type -> RuleM a -> RuleM a
bindExt x tp = bindExts [(x, tp)]

plus_l :: Num a => a -> [a] -> [a]
a `plus_l` as = map ((+) a) as

combine :: [[a]] -> ([a], [[Int]])
combine as = (concat as, foldr (\ as' is i -> [i..i + length as' - 1] : is (i + length as')) (const []) as 0)

term2fgg :: Term -> RuleM ()
term2fgg (TmVar x tp local) =
  if local then addExt x tp else okay
term2fgg (TmLam x tp tm tp') =
  getExts (bindExt x tp (term2fgg tm)) >>= \ xs' ->
  let (ns, [[itp, itp', iarr], ixs']) = combine [[tp, tp', TpArr tp tp'], map snd xs']
      es = [Edge ([itp, itp'] ++ ixs') (show tm),
            Edge [itp, itp', iarr] "v=(v1,v2)"] -- TODO
      xs = iarr : ixs' in
    addRule' (show (TmLam x tp tm tp')) ns es xs
term2fgg (TmApp tm1 tm2 tp2 tp) =
  getExts (term2fgg tm1) >>= \ xs1 ->
  getExts (term2fgg tm2) >>= \ xs2 ->
  let (ns, [[itp2, iarr, itp], ixs1, ixs2]) =
        combine [[tp2, TpArr tp2 tp, tp], map snd xs1, map snd xs2]
      es = [Edge (itp2 : ixs2) (show tm2),
            Edge (iarr : ixs1) (show tm1),
            Edge [itp2, itp, iarr] "v=(v1,v2)"] -- TODO
      xs = itp : ixs1 ++ ixs2 in
    addRule' (show (TmApp tm1 tm2 tp2 tp)) ns es xs
term2fgg (TmCase tm cs y tp) =
  getExts (term2fgg tm) >>= \ xs ->
  sequence (map (case2fgg xs (TmCase tm cs y tp)) cs) >>
  okay
term2fgg (TmSamp d y) =
  okay -- TODO

case2fgg :: [(Var, Type)] -> Term -> Case -> RuleM ()
case2fgg xs_ctm (TmCase ctm cs y tp) (Case x as xtm) =
  getExts (bindExts as (term2fgg xtm)) >>= \ xs_xtm ->
  --let ix = foldr (\ (Case x' _ _) next ix -> if x == x' then ix + 1 else next (ix + 1)) id cs 0 in
  let (ns, [[ictm, ixas, ixtm], ixs_ctm, ixs_xtm]) =
        combine [[TpVar y, TpVar y, tp], map snd xs_ctm, map snd xs_xtm]
      es = [Edge (ictm : ixs_ctm) (show ctm),
            Edge (ixas : ixtm : ixs_xtm) (show xtm),
            Edge [ictm, ixas] ("v=" ++ x)] -- TODO
      xs = ixtm : ixs_ctm ++ ixs_xtm in
    addRule' (show (TmCase ctm cs y tp)) ns es xs
case2fgg xs _ (Case x as xtm) =
  error "case2fgg expected a TmCase, but got something else"

splitArrows :: Type -> [Type]
splitArrows (TpArr tp1 tp2) = splitArrows tp1 ++ [tp2]
splitArrows (TpVar y) = [TpVar y]

getStartTerm :: Progs -> Term
getStartTerm (ProgExec tm) = tm
getStartTerm (ProgFun x tp tm ps) = getStartTerm ps
getStartTerm (ProgData y cs ps) = getStartTerm ps

prog2fgg :: Progs -> RuleM ()
prog2fgg (ProgExec tm) = term2fgg tm
prog2fgg (ProgFun x tp tm ps) =
  prog2fgg ps >> term2fgg tm >>
  addRule' x [last $ splitArrows tp] [Edge [0] (show tm)] [0]
prog2fgg (ProgData y cs ps) =
  prog2fgg ps -- TODO: add ctor rules (v=True, etc...)

file2fgg :: Progs -> FGG_JSON
file2fgg ps = rulesToFGG (\ y -> []) (show $ getStartTerm ps) (reverse $ getRules $ prog2fgg ps)
