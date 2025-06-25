-- Constructs == functions for (types containing) recursive datatypes
module Transform.RecEq (replaceEqs) where
import Struct.Lib
import Util.Helpers
import Scope.Ctxt
import Scope.Free
import Data.List (intercalate)
import Data.Map (insert, (!), intersection, toList, fromList, member, size)
import Control.Monad.RWS

-- Do a comparison, generating comparison functions
-- for types containing recursive data when necessary
replaceEq :: [Term] -> EqM Term
replaceEq [] = error "Can't have == with 0 args"
replaceEq tms@(htm : _) =
  compareTms tms
  where
    tp = typeof htm
    n = length tms

    eqName :: Type -> EqM TmName
    eqName (TpData y _ _) =
      return (TmN ("eq/" ++ show n ++ "/" ++ show y))
    eqName (TpProd Multiplicative _) =
      getEqs >>= \eqs ->
      return (TmN ("eq/" ++ show n ++ "/product/" ++ show (size eqs)))
    eqName tp = error ("eqName called on non-data, non-product type " ++ show tp)

    xname :: [Int] -> TmVar
    xname xis = TmV ('x' : intercalate "_" (map show xis))
    xtm :: [Int] -> Type -> Term
    xtm xis tp = TmVarL (xname xis) tp
    
    -- Given [tm1, ..., tmn], returns conjuction of all: True == tm1 == ... == tmn
    makeAnd [] = tmTrue
    makeAnd (tm : []) = tm
    makeAnd tms@(_ : _ : _) = TmEqs (tmTrue : tms)

    makeEq :: TmName -> Type -> EqM ()
    makeEq eqn tp =
      let ps = [(xname [i], tp) | i <- [1..n]] in
        -- Add stand-in def for now, so recursive calls work
        addEq tp n eqn ps undefined >>
        (case tp of
           TpData y [] [] -> makeEqData y
           TpProd Multiplicative tps -> makeEqProd tps
           _ -> error ("makeEq got " ++ show tp ++ " (shouldn't happen)")) >>=
        addEq tp n eqn ps

    makeEqData :: TpName -> EqM Term
    makeEqData y =
      pure (!) <*> getData <*> pure y >>= \cs ->
      pure (\cs -> TmCase (xtm [1] (TpData y [] [])) (y, [], []) cs tpBool) <*>
      mapM (\(ci, Ctor cn as) ->
              pure (Case cn [(xname [1, ci, ai], a) | (ai, a) <- zip [1..] as]) <*>
              makeCase y cs as ci)
           (zip [1..] cs)

    makeCase y cs as ci = foldr
      (\xi body ->
         pure (\cs -> TmCase (xtm [xi] (TpData y [] [])) (y, [], []) cs tpBool) <*>
         mapM (\(cj, Ctor cn as) ->
                 pure (Case cn [(xname [xi, cj, ai], a) | (ai, a) <- zip [1..] as]) <*>
                 if ci /= cj then pure tmFalse else body)
              (zip [1..] cs))
      (makeAnd <$> mapM (\(j, tp) -> compareTms [xtm [i, ci, j] tp | i <- [1..n]]) (zip [1..] as))
      [2..n]
        
    makeEqProd :: [Type] -> EqM Term
    makeEqProd tps =
      foldr
        (\i body ->
           let ps = [(xname [i, j], tp) | (j, tp) <- zip [1..] tps]
               ptp = TpProd Multiplicative tps in
             pure (TmElimMultiplicative (xtm [i] ptp) ps) <*> body <*> pure tpBool)
        (makeAnd <$>
           mapM (\(j, tp) -> compareTms [xtm [i, j] tp | i <- [1..n]]) (zip [1..] tps))
        [1..n]

    compareTms :: [Term] -> EqM Term
    compareTms [] = error "compareTms [] (shouldn't happen)"
    compareTms tms@(htm : _) =
      let tp = typeof htm in
        isFinite tp >>= \fin ->
        if fin then
          return (TmEqs tms)
        else
          isDefined tp >>= \def ->
          eqName tp >>= \eqn ->
          (if def then okay else makeEq eqn tp) >>
          return (TmVarG GlDefine eqn [] [] [(tm, tp) | tm <- tms] tpBool)

    isFinite :: Type -> EqM Bool
    isFinite tp = getCtxt >>= \g -> return (not (isInfiniteType g tp))

    isDefined :: Type -> EqM Bool
    isDefined tp = member (tp, n) <$> getEqs

type EqM = RWS (Map TpName [Ctor]) () (Map (Type, Int) (TmName, [Param], Term))

getData :: EqM (Map TpName [Ctor])
getData = ask

getEqs :: EqM (Map (Type, Int) (TmName, [Param], Term))
getEqs = get

addEq :: Type -> Int -> TmName -> [Param] -> Term -> EqM ()
addEq tp n x ps tm = modify (insert (tp, n) (x, ps, tm))

getCtxt :: EqM Ctxt
getCtxt = getData >>= \ds -> return (emptyCtxt {tpNames = fmap (CtData [] []) ds})

replaceEqsh :: Term -> EqM Term
replaceEqsh (TmVarL x tp) =
  pure (TmVarL x tp)
replaceEqsh (TmVarG gl x ts ps as tp) =
  pure (TmVarG gl x ts ps) <*> mapArgsM replaceEqsh as <*> pure tp
replaceEqsh (TmLam x xtp tm tp) =
  pure (TmLam x xtp) <*> replaceEqsh tm <*> pure tp
replaceEqsh (TmApp tm1 tm2 tp2 tp) =
  pure TmApp <*> replaceEqsh tm1 <*> replaceEqsh tm2 <*> pure tp2 <*> pure tp
replaceEqsh (TmLet x xtm xtp tm tp) =
  pure (TmLet x) <*> replaceEqsh xtm <*> pure xtp <*> replaceEqsh tm <*> pure tp
replaceEqsh (TmCase tm tpd cs rtp) =
  pure TmCase <*> replaceEqsh tm <*> pure tpd <*> mapCasesM (\_ _ -> replaceEqsh) cs <*> pure rtp
replaceEqsh (TmAmb tms tp) =
   pure TmAmb <*> mapM replaceEqsh tms <*> pure tp
replaceEqsh (TmFactorDouble p tm tp) =
   pure (TmFactorDouble p) <*> replaceEqsh tm <*> pure tp
replaceEqsh (TmFactorNat p tm tp) =
   pure (TmFactorNat p) <*> replaceEqsh tm <*> pure tp
replaceEqsh (TmFactorRatio p tm tp) =
   pure (TmFactorRatio p) <*> replaceEqsh tm <*> pure tp
replaceEqsh (TmProd am as) =
  pure (TmProd am) <*> mapArgsM replaceEqsh as
replaceEqsh (TmElimMultiplicative xtm xps tm tp) =
  pure TmElimMultiplicative <*> replaceEqsh xtm <*> pure xps <*> replaceEqsh tm <*> pure tp
replaceEqsh (TmElimAdditive xtm xi xj xp tm tp) =
  pure TmElimAdditive <*> replaceEqsh xtm <*> pure xi <*> pure xj <*> pure xp <*> replaceEqsh tm <*> pure tp
replaceEqsh (TmEqs tms) = replaceEq tms
    
replaceEqsProg :: Prog -> EqM Prog
replaceEqsProg (ProgDefine x ps tm tp) =
  pure (ProgDefine x ps) <*> replaceEqsh tm <*> pure tp
replaceEqsProg p = pure p

replaceEqsProgs :: Progs -> EqM Progs
replaceEqsProgs (Progs ps tm) =
  pure Progs <*> mapM replaceEqsProg ps <*> replaceEqsh tm

replaceEqs :: Progs -> Progs
replaceEqs p =
  let g = ctxtAddProgs p
      r = fmap (\(CtData _ _ cs) -> cs) (tpNames g)
      (Progs ps tm, s, ()) = runRWS (replaceEqsProgs p) r mempty
      eqps = [ProgDefine x pms tm tpBool | ((y, i), (x, pms, tm)) <- toList s]
  in
    Progs (ps ++ eqps) tm
