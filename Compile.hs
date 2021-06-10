module Compile where
import Data.List
import Exprs
import FGG
import Check

type External = (Var, Type)
data RuleM = RuleM [Rule] [External]

infixl 1 +>=, +>
(+>=) :: RuleM -> ([External] -> RuleM) -> RuleM
RuleM rs xs +>= f = let RuleM rs' xs' = f xs in RuleM (rs ++ rs') (xs ++ xs')

(+>) :: RuleM -> RuleM -> RuleM
r1 +> r2 = r1 +>= \ _ -> r2

addExts :: [(Var, Type)] -> RuleM
addExts xs = RuleM [] xs

addExt :: Var -> Type -> RuleM
addExt x tp = addExts [(x, tp)]

addRules :: [Rule] -> RuleM
addRules rs = RuleM rs []

addRule :: Rule -> RuleM
addRule r = addRules [r]

addRule' :: String -> [Type] -> [Edge] -> [Int] -> RuleM
addRule' lhs ns es xs = addRule $ Rule lhs $ HGF (map show ns) es xs

returnRule :: RuleM
returnRule = RuleM [] []

-- Local var rule
var2fgg :: Var -> Type -> RuleM
var2fgg x tp =
  addRule' x [tp, tp] [Edge [0, 1] ("=" ++ show tp)] [0, 1]

getRules :: RuleM -> [Rule]
getRules (RuleM rs xs) = rs

bindExts :: [(Var, Type)] -> RuleM -> RuleM
bindExts xs' (RuleM rs xs) =
  let keep = flip elem (map fst xs') . fst in
  foldr (\ (x, tp) r -> var2fgg x tp +> r) (RuleM rs (filter keep xs)) xs'

bindExt :: Var -> Type -> RuleM -> RuleM
bindExt x tp = bindExts [(x, tp)]

plus_l :: Num a => a -> [a] -> [a]
a `plus_l` as = map ((+) a) as

combine :: [[a]] -> ([a], [[Int]])
combine as = (concat as, foldr (\ as' is i -> [i..i + length as' - 1] : is (i + length as')) (const []) as 0)

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

tmapp2fgg :: Term -> RuleM
tmapp2fgg (TmApp tm1 tm2 tp2 tp) =
  term2fgg tm1 +>= \ xs1 ->
  term2fgg tm2 +>= \ xs2 ->
  let (ns, [[itp2, itp, iarr], ixs1, ixs2]) =
        combine [[tp2, tp, TpArr tp2 tp], map snd xs1, map snd xs2]
      es = [Edge (itp2 : ixs2) (show tm2),
            Edge (iarr : ixs1) (show tm1),
            Edge [itp2, itp, iarr] "v=(v1,v2)"]
      xs = itp : ixs1 ++ ixs2 in
    addRule' (show (TmApp tm1 tm2 tp2 tp)) ns es xs

ctorEtaName :: Var -> Int -> Var
ctorEtaName x i = show i ++ x

ctorVar2fgg :: Var -> Type -> RuleM
ctorVar2fgg x tp =
  let tps' = splitArrows tp
      --end = last tps'
      tps = dropFromEnd 1 tps'
      etas = map (ctorEtaName x) [0..length tps - 1]
      (atm, [end]) = foldl (\ (tm, (atp : tps)) a -> (TmApp tm (TmVar a atp ScopeLocal) atp (joinArrows tps), tps)) (TmVar x tp ScopeCtor, tps') etas
      ltm = foldr (\ a f (atp : tps) -> TmLam a atp (f tps) (joinArrows tps)) (const $ TmFGGBreak atm) etas tps' in
    term2fgg ltm

getCtorArgs :: Term -> [(Var, Type)]
getCtorArgs (TmVar x tp sc) = []
getCtorArgs (TmApp tm (TmVar x tp ScopeLocal) _ _) = (x, tp) : getCtorArgs tm

ctor2fgg :: Ctor -> Var -> RuleM
ctor2fgg (Ctor x as) y =
  let as' = map (ctorEtaName x) [0..length as - 1]
      (ns, [ias1, ias2, [iy]]) = combine [as, as, [TpVar y]]
      ias = zip3 ias1 ias2 as'
      es_as = map (\ (ia1, ia2, a) -> Edge [ia1, ia2] a) ias
      es = Edge (iy : ias2) ("v=" ++ x) : es_as
      xs = iy : ias1 in
    addRule' x ns es xs

case2fgg :: [(Var, Type)] -> Term -> Case -> RuleM
case2fgg xs_ctm (TmCase ctm cs y tp) (Case x as xtm) =
  bindExts as (term2fgg xtm) +>= \ xs_xtm ->
  --let ix = foldr (\ (Case x' _ _) next ix -> if x == x' then ix + 1 else next (ix + 1)) id cs 0 in
  let (ns, [[ictm, ixtm], ixs_as, ixs_ctm, ixs_xtm]) =
        combine [[TpVar y, tp], map snd as, map snd xs_ctm, map snd xs_xtm]
      es = [Edge (ictm : ixs_ctm) (show ctm),
            Edge (ixtm : ixs_xtm ++ ixs_as) (show xtm),
            Edge (ictm : ixs_as) ("v=" ++ x)]
      xs = ixtm : ixs_ctm ++ ixs_xtm in
    addRule' (show (TmCase ctm cs y tp)) ns es xs
case2fgg xs _ (Case x as xtm) =
  error "case2fgg expected a TmCase, but got something else"

--stopApp :: Term -> Type -> Term
--stopApp tm tp = TmApp tm (TmVar " ___STOP___ " (TpVar " ___STOP___ ") ScopeGlobal) (TpVar " ___STOP___ ") tp

term2fgg :: Term -> RuleM
--term2fgg (TmApp tm (TmVar " ___STOP___ " (TpVar " ___STOP___ ") ScopeGlobal) (TpVar " ___STOP___ ") tp) =
term2fgg (TmFGGBreak tm) =
  addExts (getCtorArgs tm)
term2fgg (TmVar x tp local) =
  case local of
    ScopeGlobal -> returnRule
    ScopeLocal -> addExt x tp
    ScopeCtor -> ctorVar2fgg x tp
term2fgg (TmLam x tp tm tp') =
  bindExt x tp (term2fgg tm) +>= \ xs' ->
  let (ns, [[itp, itp', iarr], ixs']) = combine [[tp, tp', TpArr tp tp'], map snd xs']
      es = [Edge ([itp, itp'] ++ ixs') (show tm),
            Edge [itp, itp', iarr] "v=(v1,v2)"]
      xs = iarr : ixs' in
    addRule' (show (TmLam x tp tm tp')) ns es xs
term2fgg (TmApp tm1 tm2 tp2 tp) =
  tmapp2fgg (TmApp tm1 tm2 tp2 tp)
--  case splitApps (TmApp tm1 tm2 tp2 tp) of
--    (((TmVar x xtp ScopeCtor), TpVar y), as) -> ctor2fgg x xtp y as
--    _ -> tmapp2fgg (TmApp tm1 tm2 tp2 tp)
term2fgg (TmCase tm cs y tp) =
  term2fgg tm +>= \ xs ->
  foldr (\ c r -> case2fgg xs (TmCase tm cs y tp) c +> r) returnRule cs
term2fgg (TmSamp d y) =
  returnRule -- TODO

getStartTerm :: Progs -> Term
getStartTerm (ProgExec tm) = tm
getStartTerm (ProgFun x tp tm ps) = getStartTerm ps
getStartTerm (ProgData y cs ps) = getStartTerm ps

prog2fgg :: Progs -> RuleM
prog2fgg (ProgExec tm) = term2fgg tm
prog2fgg (ProgFun x tp tm ps) =
  prog2fgg ps +> term2fgg tm +>
  addRule' x [last $ splitArrows tp] [Edge [0] (show tm)] [0]
prog2fgg (ProgData y cs ps) =
  prog2fgg ps +>
  foldr (\ c r -> r +> ctor2fgg c y) returnRule cs

file2fgg :: Progs -> FGG_JSON
file2fgg ps = rulesToFGG (\ y -> []) (show $ getStartTerm ps) (reverse $ getRules $ prog2fgg ps)
