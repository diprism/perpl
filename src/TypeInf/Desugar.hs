{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant fmap" #-}
{-# HLINT ignore "Use lambda-case" #-}
module TypeInf.Desugar where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Except
import Control.Monad.RWS.Lazy
import Data.List (intercalate)
import Scope.Subst (Subst(tmVars, tpVars, tags), STerm(Replace), FreeVars(freeTmVars, freeTpVars), subst, freeVars, freeDatatypes, substTags)
import Scope.Free (robust, positive, isAff)
import Scope.Fresh (newVar)
import Scope.Ctxt
import Struct.Exprs
import Struct.Helpers
import TypeInf.Check
import TypeInf.Solve
import Util.Graph (scc, SCC(..))
import Util.Helpers ( listDifference, okay )

{-
Let's de-sugar in a new mini-phase!
1. Read through a file, and while it is reading...
2. Recognize any UsProgData's that appear (those represent data structures like Lists).
3. See if the UsProgData is used by a case (for now) (later we'll get into lambda's and let's).
4. If the answer to 3. is yes, then de-sugar that case (or lambda or let),
  since it is here that we can deduce that Nil is a List, Cons is a List, etc.
  Ex: For case's, it is in seeing a Nil case that we can deduce the thing being case'd is a List.
5. We may have to make small, effortless changes to progBuiltIns and ctxtAddUsProgs, which come before this mini-phase
(in order to get input and output types correct).

RECALL in Struct.Exprs, individual user-level definitions of data structures go like this:
data UsProg = UsProgData TpName [TpVar] [Ctor]    -- lhs, type params, constructors
That last part, the [Ctor], is a list storing all the possible constructors!
We can use that to determine if we are missing any cases,
and know how to de-sugar into the correct constructors.

also RECALL these definitions:
1. UsCase UsTm [CaseUs]                     -- case tm of case*
2. data CaseUs = CaseUs TmName [TmVar] UsTm -- | x a1 ... an -> tm
3. data Case = Case TmName [Param] Term     -- | x (a1 : tp1) ... (an : tpn) -> tm
-}

-- If false, throw error e
guardM' :: Bool -> TypeError -> a 
guardM' True e = ()
guardM' False e = ask >>= (\ loc -> throwError (e, loc)) . checkLoc

-- Lookup a datatype
lookupDatatype' :: TpName -> ([Tag], [TpVar], [Ctor])
lookupDatatype' x =
  ask >>= (\ g ->
  case Map.lookup x (tpNames g) of
    Just (CtData tgs ps cs) -> (tgs, ps, cs)
    _ -> ask >>= (\ loc -> throwError (ScopeError (show x), loc)) . checkLoc) . checkEnv

-- Lookup the datatype that cases split on
lookupCtorType' :: [CaseUs] -> (TpName, [Tag], [TpVar], [Ctor])
lookupCtorType' [] = ask >>= (\ loc -> throwError (NoCases, loc)) . checkLoc
lookupCtorType' (CaseUs x _ _ : _) =
  ask >>= (\ d ->
  case d of
    Just (CtCtor _ _ ctp) -> case splitArrows ctp of
      (_, TpData y _ _) -> let (tgs, xs, cs) = lookupDatatype' y in (y, tgs, xs, cs)
      (_, etp) -> error "This shouldn't happen"
    _ -> ask >>= (\ loc -> throwError (CtorError x, loc)) . checkLoc) . fmap (Map.lookup x . tmNames) checkEnv

-- Infers/checks a term, elaborating it from a user-term (UsTm) to a full Term
desugar' :: UsTm -> UsTm
desugar' (UsCase tm cs) =
  -- (CALCULATES the missing cases by running lookupCtorType to get the constructors this type is supposed to have)
  -- (EX: can deduce that a List is either a Nil or a Cons)
  let (y, tgs, ps, ctors) = lookupCtorType' cs in -- lookup the datatype we have cases for
    let missingCases = listDifference [y | (Ctor y _) <- ctors] [x | (CaseUs x _ _) <- cs] in -- here we're saying that missing cases = ctors - cases
      guardM' (null missingCases) (MissingCases missingCases) >> -- guard against missing cases
      guardM' (length ctors == length cs) (WrongNumCases (length ctors) (length cs)) >> -- guard against wrong # of cases
      return (UsCase tm cs)

termToProg :: UsTm -> UsProgs
termToProg = UsProgs []

-- Desugars an entire program
desugarProgs :: UsProgs -> UsProgs
desugarProgs (UsProgs xs term) = termToProg (desugar' term)

-- Try to desugar an entire file
desugarFile :: UsProgs -> Either String UsProgs
desugarFile ps
  | ps < 2 = Left "desugar error"
  | otherwise = Right (desugarProgs ps)

{-
desugarFile ps =
  either (\ (e, loc) -> Left (if null (show loc) then show e else show e ++ ", " ++ show loc))
         (\ (a, s, w) -> Right a)
    (runExcept (runRWST (desugarProgs ps)
                        (CheckR emptyCtxt (Loc Nothing "")) mempty))
-}