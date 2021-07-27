module RecType where
import qualified Data.Map as Map
import qualified Control.Monad.State.Lazy as State
import Exprs
import Util
import Free
import Ctxt
import Name


isRecType' :: Ctxt -> Var -> [Type] -> Bool
isRecType' g y = h [] where
  h :: [Var] -> [Type] -> Bool
  h hist [] = False
  h hist (TpArr tp1 tp2 : tps) = h hist (tp1 : tp2 : tps)
  h hist (TpVar y' : tps)
    | y == y' = True
    | y' `elem` hist = h hist tps
    | otherwise = maybe
      (h hist tps)
      (\ cs -> h (y' : hist) (foldr (\ (Ctor x as) tps -> as ++ tps) tps cs))
      (ctxtLookupType g y')
  h hist (TpMaybe tp : tps) = h hist (tp : tps)
  h hist (TpBool : tps) = h hist tps

isRecDatatype :: Ctxt -> Var -> Bool
isRecDatatype g y =
  maybe False (isRecType' g y . concat . map (\ (Ctor _ tp) -> tp)) (ctxtLookupType g y)

isRecType :: Ctxt -> Type -> Bool
isRecType g (TpVar y) = isRecDatatype g y
isRecType g _ = False

getRecTypes' :: Ctxt -> [Prog] -> [Var]
getRecTypes' g (ProgData y cs : ds) =
  if isRecDatatype g y then y : getRecTypes' g ds else getRecTypes' g ds
getRecTypes' g (ProgFun x ps tm tp : ds) = getRecTypes' g ds
getRecTypes' g (ProgExtern x xp ps tp : ds) = getRecTypes' g ds
getRecTypes' g [] = []

getRecTypes :: Ctxt -> Progs -> [Var]
getRecTypes g (Progs ds end) = getRecTypes' g ds

-- N.B. state list is in reverse order
type DisentangleResult = (Map.Map Var Type, Var, Type, [Case], Type)
type DisentangleState = [DisentangleResult]
type DisentangleM a = State.State DisentangleState a

disentangleTerm :: [Type] -> Term -> DisentangleM Term
disentangleTerm recs = h where
  h :: Term -> DisentangleM Term
  h (TmVarL x tp) = pure (TmVarL x tp)
  h (TmVarG gv x as tp) =
    pure (TmVarG gv x)
      <*> mapM (\ (atm, atp) -> fmap (flip (,) atp) (h atm)) as
      <*> pure tp
  h (TmLam x tp tm tp') =
    pure (TmLam x tp) <*> h tm <*> pure tp'
  h (TmApp tm1 tm2 tp2 tp) =
    pure TmApp <*> h tm1 <*> h tm2 <*> pure tp2 <*> pure tp
  h (TmLet x xtm xtp tm tp) =
    pure (TmLet x) <*> h xtm <*> pure xtp <*> h tm <*> pure tp
  h (TmCase tm tp1 cs tp2)
    | tp1 `elem` recs =
      h tm >>= \ tm' ->
      mapM (\ (Case x as tm) -> pure (Case x as) <*> h tm) cs >>= \ cs' ->
      State.get >>= \ unfolds ->
      let fvs = freeVars' (TmCase (TmVarG DefVar "" [] tp1) tp1 cs' tp2)
          fvs' = Map.toList fvs
          --ptp = joinArrows (map snd fvs') tp2
          name = applyName (length unfolds)
          rtm = TmVarG DefVar name ((tm', tp1) : toTermArgs fvs') tp2 in
        State.put ((fvs, name, tp1, cs', tp2) : unfolds) >>
        pure rtm
    | otherwise =
      pure TmCase <*> h tm <*> pure tp1
        <*> mapM (\ (Case x xas xtm) -> pure (Case x xas) <*> h xtm) cs <*> pure tp2
  h (TmSamp d tp) =
    pure (TmSamp d tp)
  h (TmFold fuf tm tp) =
    pure (TmFold fuf) <*> h tm <*> pure tp

disentangleProg :: [Type] -> Prog -> DisentangleM Prog
disentangleProg recs (ProgFun x ps tm tp) =
  pure (ProgFun x ps) <*> disentangleTerm recs tm <*> pure tp
disentangleProg recs (ProgExtern x xp ps tp) =
  pure (ProgExtern x xp ps tp)
disentangleProg recs (ProgData y cs) =
  pure (ProgData y cs)

disentangleProgs' :: [Type] -> Progs -> DisentangleM Progs
disentangleProgs' recs (Progs ps end) =
  pure Progs <*> mapM (disentangleProg recs) ps <*> disentangleTerm recs end

disentangleMake :: Int -> DisentangleResult -> Prog
disentangleMake i (fvs, name, tp, cs, tp') =
  let tname = applyTargetName i
      as = (tname, tp) : Map.toList fvs
      rtm = TmCase (TmVarL tname tp) tp cs tp' in
    ProgFun name as rtm tp

disentangleProgs :: [Type] -> Progs -> DisentangleM Progs
disentangleProgs recs p =
  disentangleProgs' recs p >>= \ (Progs ps end) ->
  State.get >>= \ unfolds ->
  let unfolds' = enumerate (reverse unfolds)
      apply_ps = map (uncurry disentangleMake) unfolds' in
  return (Progs (ps ++ apply_ps) end)

disentangleRun :: [Type] -> ([Type] -> a -> DisentangleM a) -> a -> (a, DisentangleState)
disentangleRun recs f a = fmap reverse (State.runState (f recs a) [])

disentangleFile :: Progs -> Either String (Progs, [Var])
disentangleFile ps =
  let g = ctxtDefProgs ps
      recs = map TpVar (getRecTypes g ps) in
    return (fmap (map (\ (_, name, _, _, _) -> name))
            (disentangleRun recs disentangleProgs ps))

elimRecTypes :: (Progs, [Var]) -> Either String Progs
elimRecTypes (ps, apply_fs) = return ps
