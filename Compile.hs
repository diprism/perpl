module Compile where
import Exprs
import FGG
import Check

splitArrows :: Type -> [Type]
splitArrows (TpArr tp1 tp2) = splitArrows tp1 ++ [tp2]
splitArrows (TpVar y) = [TpVar y]

-- Local var rule
var2fgg :: Var -> Type -> Rule
var2fgg x tp = Rule x (HGF [show tp, show tp] [Edge [0, 1] "="] [0, 1])

term2fgg :: Term -> [Rule]
term2fgg (TmVar x tp) =
  [] -- rules for local vars get added when bound, global vars when defined
term2fgg (TmLam x tp tm tp') =
  let ns = [show tp, show tp', show (TpArr tp tp')]
      es = [Edge [0, 1   ] (show tm),
            Edge [0, 1, 2] (x ++ "=(" ++ x ++ "1," ++ x ++ "2)")]
      lamRule = Rule (show (TmLam x tp tm tp')) (HGF ns es [2]) in
    lamRule : var2fgg x tp : term2fgg tm
term2fgg (TmApp tm1 tm2 tp2 tp) =
  Rule (show (TmApp tm1 tm2 tp2 tp))
       (HGF [show (TpArr tp2 tp), show tp2, show tp]
            [Edge [0] (show tm1),
             Edge [1] (show tm2),
             Edge [1, 2, 0] "TODO=(TODO1, TODO2)"]
            [2]) :
  term2fgg tm1 ++ term2fgg tm2
term2fgg (TmCase tm cs y tp) =
  foldr (\ c rs -> case2fgg (TmCase tm cs y tp) c ++ rs) (term2fgg tm) cs
term2fgg (TmSamp d y) = [] -- TODO

case2fgg :: Term -> Case -> [Rule]
case2fgg (TmCase tm cs y tp) (Case x as xtm) =
  let ix = foldr (\ (Case x' _ _) next ix ->
                    if x == x' then ix + 1 else next (ix + 1)) id cs 0
      ns = ([y, y, show tp] ++ map (\ (a, atp) -> show atp) as)
      e1 = Edge [0] (show xtm)
      e2 = Edge [0, 1] ("TODO" ++ "=(" ++ show ix ++ "," ++ "TODO" ++ ")")
      e3 = Edge [1..(length ns) - 1] (show xtm) in
  Rule (show $ TmCase tm cs y tp) (HGF ns [e1, e2, e3] [0, 1]) :
    foldr (\ (a, atp) rs -> var2fgg a atp : rs) (term2fgg xtm) as
case2fgg _ (Case x as xtm) = error "case2fgg needs a TmCase, but got something else"

getStartSymbol :: Progs -> String
getStartSymbol (ProgExec tm) = show tm
getStartSymbol (ProgFun x tp tm ps) = getStartSymbol ps
getStartSymbol (ProgData y cs ps) = getStartSymbol ps

prog2fgg :: Progs -> [Rule]
prog2fgg (ProgExec tm) = term2fgg tm
prog2fgg (ProgFun x tp tm ps) =
  Rule x (HGF [show $ last $ splitArrows tp] [Edge [0] (show tm)] [0]) :
    term2fgg tm ++ prog2fgg ps
prog2fgg (ProgData y cs ps) = prog2fgg ps -- TODO: do datatypes have rules?

file2fgg :: Progs -> FGG_JSON
file2fgg ps = rulesToFGG (\ y -> []) (getStartSymbol ps) (prog2fgg ps)
