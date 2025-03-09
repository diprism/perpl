{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Replace case with fromMaybe" #-}
{-# HLINT ignore "Monad law, left identity" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
module Main where
import Control.Monad (foldM)
import System.Console.GetOpt
import System.Exit (die, exitSuccess)
import System.Environment (getArgs, getProgName)
import System.IO (hPutStr, hPutStrLn, stdin, stdout, stderr, openFile, IOMode(..), hGetContents, hFlush)
import Struct.Lib (TpName(TpN), Progs, progBuiltins)
import Parse.Lib (parse)
import TypeInf.Lib (infer)
import Compile.Lib (compileFile)
import Transform.Monomorphize (monomorphizeFile)
import Transform.DR (elimRecTypes, DeRe(..))
import Transform.AffLin (affLinFile)
import Transform.Optimize (optimizeFile)
import Transform.Argify (argifyFile)
import Transform.RecEq (replaceEqs)
import Scope.Subst (Substitutable, alphaRename)
import Scope.Ctxt (ctxtAddProgs, ctxtAddUsProgs, Ctxt)
import Util.FGG (showFGG, FGG)
import Util.SumProduct (sumProduct, prettySumProduct)
import Util.Indices (PatternedTensor)

data CmdArgs = CmdArgs {
  optInfile :: Maybe String,
  optOutfile :: Maybe String,
  optCompile :: Bool,
  optElimRecs :: Bool,
  optDerefun :: [(TpName, DeRe)],
  optLin :: Bool,
  optOptimize :: Bool,
  optSumProduct :: Bool,
  optPrettySumProduct :: Bool,
  optSuppressInterp :: Bool
}

optionsDefault = CmdArgs {
  optInfile = Nothing,
  optOutfile = Nothing,
  optCompile = True,
  optElimRecs = True,
  optDerefun = [],
  optLin = True,
  optOptimize = True,
  optSumProduct = False,
  optPrettySumProduct = False,
  optSuppressInterp = False
}

options :: [OptDescr (CmdArgs -> Either String CmdArgs)]
options = -- Option: list of short option chars, list of long option strings, arg descriptor, and explanation of option for user
  [Option ['m'] [] (NoArg (\ opts -> return (opts {optLin = False})))
     "Stop after monomorphizing (won't linearize, won't eliminate recursive datatypes, will compile only to PPL code)",
   Option ['l'] [] (NoArg (\ opts -> return (opts {optElimRecs = False})))
     "Stop afer linearizing (won't eliminate recursive datatypes, will compile only to PPL code)",
   Option ['e'] [] (NoArg (\ opts -> return (opts {optCompile = False})))
     "Stop after eliminating recursive datatypes",
   Option ['c'] [] (NoArg (\ opts -> return (opts {optCompile = False})))
     "Stop after compiling to final-stage PPL code (not to FGG)",
   Option ['z'] [] (NoArg (\ opts -> return (opts {optSumProduct = True})))
     "Compute sum-product",
   Option ['p'] [] (NoArg (\ opts -> return (opts {optSumProduct = True, optPrettySumProduct = True}))) -- if only -p is given, set both optSumProduct and optPrettySumProduct to True
     "Compute sum-product with cleaner output",
   Option ['s'] [] (NoArg (\ opts -> return (opts {optSuppressInterp = True})))
     "Suppress values in the output JSON (no effect if no JSON output)",
   Option ['o'] [] (ReqArg processOutfileArg "OUTFILE")
     "Output to OUTFILE",
   Option ['O'] [] (ReqArg processOptimArg "LEVEL")
     "Optimization level (0 = off, 1 = on)",
   Option ['d'] [] (ReqArg (\ d opts -> return (opts {optDerefun = (TpN d, Defun) : optDerefun opts})) "DTYPE")
     "Defunctionalize recursive datatype DTYPE",
   Option ['r'] [] (ReqArg (\ d opts -> return (opts {optDerefun = (TpN d, Refun) : optDerefun opts})) "DTYPE")
     "Refunctionalize recursive datatype DTYPE"]

-- Flag -O, set optimization level
processOptimArg :: String -> CmdArgs -> Either String CmdArgs
processOptimArg level opts = case level of
  "0" -> Right (opts { optOptimize = False })
  "1" -> Right (opts { optOptimize = True })
  _ -> Left "invalid optimization level (valid levels are 0 and 1)\n"

-- Flag -o, set output file
processOutfileArg :: String -> CmdArgs -> Either String CmdArgs
processOutfileArg fn opts = case optOutfile opts of
  Nothing -> Right (opts {optOutfile = Just fn})
  Just _ -> Left "at most one output filename allowed\n"

-- Ensure only one input filename is given in argv
processInfileArg :: String -> CmdArgs -> Either String CmdArgs
processInfileArg fn opts = case optInfile opts of
  Nothing -> Right (opts {optInfile = Just fn})
  Just _ -> Left "at most one input filename allowed\n"

processArgs :: [String] -> Either String CmdArgs
processArgs argv =
  case getOpt Permute options argv of -- case (option args, list of non-options, list of error messages) of
    (o, [], errs) -> -- catch if there is an empty list of non-options
      Left (let safeHead errors = if null errors then Nothing else Just (head errors) in
            case safeHead errs of -- safer head function for handling errs
              Just e -> e
              Nothing -> "")
    (o, n, []) ->
      foldM (flip processInfileArg) optionsDefault n >>= \ opts' ->
      foldM (flip id) opts' o
    (_, _, errs) ->
      Left (let safeHead errors = if null errors then Nothing else Just (head errors) in
            case safeHead errs of -- safer head function for handling errs
              Just e -> e
              Nothing -> "")

putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr

doIf :: Bool -> (a -> Either String a) -> a -> Either String a
doIf True f = f
doIf False f = return

showFile :: Progs -> Either String String
showFile = return . show

alphaRenameProgs :: Substitutable p => (p -> Ctxt) -> p -> Either String p
alphaRenameProgs gf a = return (alphaRename (gf a) a)

-- Process command-line arguments (options) and input
processContents :: CmdArgs -> String -> Either String String
processContents (CmdArgs ifn ofn c e dr l o z p si) s =
  let e' = e && l
      c' = c && e'
  in
  return s
  -- String to UsProgs
  >>= parse
  -- Pick a unique name for each bound var (TODO: is this really needed?)
  >>= alphaRenameProgs ctxtAddUsProgs
  -- Add Bool, True, False
  >>= Right . progBuiltins
  -- Type check the file (:: UsProgs -> Progs)
  >>= infer
  >>= (\ x -> (Right . monomorphizeFile) x
  >>= Right . argifyFile
  >>= Right . replaceEqs -- TODO: move before monomorphization, relax == constraints in Check (but this isn't so simple: what about List A == List A vs List (List A) == List (List A)?)
--  >>= alphaRenameProgs (const emptyCtxt)
  -- Apply various optimizations
  >>= doIf o optimizeFile
  -- Convert terms from affine to linear
  >>= doIf l affLinFile
  -- Replace == of recursive datatypes
  -- Eliminate recursive types (de/refunctionalization)
  >>= doIf e' (elimRecTypes dr)
  -- Apply various optimizations (again) (disabled for now; joinApps problem after aff2lin introduces maybe types)
  >>= doIf o optimizeFile
  -- Pick a unique name for each bound var (again), needed by compileFile
  >>= alphaRenameProgs ctxtAddProgs
  -- Compile to FGG
  >>= if c' then
        \ps -> if z then if p then prettySumProduct <$> compileFile ps
                              else show . sumProduct <$> compileFile ps
                    else (showFGG si :: FGG PatternedTensor -> String) <$> compileFile ps
      else
        showFile
                                       )

-- Parse a file, check and elaborate it, then compile to FGG and output it
main :: IO ()
main = getArgs >>= \ argv -> case processArgs argv of
  Right opts ->
    maybe (return stdin) (\ fn -> openFile fn ReadMode) (optInfile opts) >>= \ifh ->
    maybe (return stdout) (\ fn -> openFile fn WriteMode) (optOutfile opts) >>= \ofh ->
    hGetContents ifh >>= \ input ->
    either die (\ a -> hPutStr ofh a >> hFlush ofh >> exitSuccess) (processContents opts input)    

  Left err ->
    getProgName >>= \ name ->
    putStrLnErr (name ++ ": " ++ err ++ usageInfo ("usage: " ++ name ++ " [OPTION ...] INFILE.ppl") options)
