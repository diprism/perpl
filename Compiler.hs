module Compiler where
import Exprs

{-
    TmVar Var
  | TmLam FnQual Var Type Term
  | TmApp Term Term
  | TmLet Var Type Term Term
  | TmSamp Term
  | TmObs Term Term
  | TmFail
  | TmBool Bool
  | TmIf Term Term Term
  | TmInj InjLR
  | TmCase Term Var Term Var Term
  | TmUnit
-}

--aff2lin :: Term -> Term
aff2lin (TmVar x) = x
aff2lin (TmLam FnAff x tp tm) = TmIf (TmSamp TmAmb) () ()
