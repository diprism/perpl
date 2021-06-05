module Compile where
import Exprs
import Ctxt
import FGG
import Check

--ppl2fgg :: Progs -> FGG -> FGG
--ppl2fgg (ProgExec tm) fgg = ()
--ppl2fgg (ProgFun x tp tm ps) fgg = ()
--ppl2fgg (ProgData y cs ps) fgg = ()

{-
    TmVar Var Type
  | TmLam Var Type Term Type
  | TmApp Term Term Type {- -> -} Type
  | TmCase Term [Case] Var Type
  | TmSamp Dist Var
-}



term2fgg :: Ctxt -> Term -> FGG_JSON -> FGG_JSON
term2fgg g (TmVar x tp) fgg = fgg -- TODO
term2fgg g (TmLam x tp tm tp') fgg = fgg -- TODO
term2fgg g (TmApp tm1 tm2 tp2 tp) fgg = fgg -- TODO
term2fgg g (TmCase tm cs y tp) fgg = fgg -- TODO
term2fgg g (TmSamp d y) fgg = fgg -- TODO
