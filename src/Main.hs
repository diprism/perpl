module Main where
import Control.Monad (foldM)
import System.Console.GetOpt
import System.Exit (die, exitSuccess)
import System.Environment (getArgs, getProgName)
import System.IO (hPutStr, hPutStrLn, stdin, stdout, stderr, openFile, IOMode(..), hGetContents)
import Struct.Lib (TpName(TpN), Progs, progBuiltins)
import Parse.Lib
import TypeInf.Lib
import Compile.Lib
import Transform.Monomorphize
import Transform.DR
import Transform.AffLin
import Transform.Optimize
import Transform.Argify
import Scope.Subst (Substitutable, alphaRename)
import Scope.Ctxt
import Util.FGG
import Util.SumProduct

data CmdArgs = CmdArgs {
  optInfile :: Maybe String,
  optOutfile :: Maybe String,
  optCompile :: Bool,
  optMono :: Bool,
  optElimRecs :: Bool,
  optDerefun :: [(TpName, DeRe)],
  optLin :: Bool,
  optOptimize :: Bool,
  optSumProduct :: Bool
}

optionsDefault = CmdArgs {
  optInfile = Nothing,
  optOutfile = Nothing,
  optCompile = True,
  optMono = True,
  optElimRecs = True,
  optDerefun = [],
  optLin = True,
  optOptimize = True,
  optSumProduct = False
}

options =
  [Option ['m'] [] (NoArg (\ opts -> return (opts {optMono = False})))
     "Don't monomorphize (implies -lec)",
   Option ['l'] [] (NoArg (\ opts -> return (opts {optLin = False})))
     "Don't linearize (implies -ec)",
   Option ['e'] [] (NoArg (\ opts -> return (opts {optElimRecs = False})))
     "Don't eliminate recursive datatypes (implies -c)",
   Option ['c'] [] (NoArg (\ opts -> return (opts {optCompile = False})))
     "Compile only to PPL code (not to FGG)",
   Option ['z'] [] (NoArg (\ opts -> return (opts {optSumProduct = True})))
     "Compute sum-product",
   Option ['o'] [] (ReqArg processOutfileArg "OUTFILE")
     "Output to OUTFILE",
   Option ['O'] [] (ReqArg processOptimArg "LEVEL")
     "Optimization level (0 = off, 1 = on)",
   Option ['d'] [] (ReqArg (\ d opts -> return (opts {optDerefun = (TpN d, Defun) : optDerefun opts})) "DTYPE")
     "Defunctionalize recursive datatype DTYPE",
   Option ['r'] [] (ReqArg (\ d opts -> return (opts {optDerefun = (TpN d, Refun) : optDerefun opts})) "DTYPE")
     "Refunctionalize recursive datatype DTYPE"]

processOptimArg :: String -> CmdArgs -> Either String CmdArgs
processOptimArg level opts = case level of
  "0" -> Right (opts { optOptimize = False })
  "1" -> Right (opts { optOptimize = True })
  _ -> Left "invalid optimization level (valid levels are 0 and 1)\n"

processOutfileArg :: String -> CmdArgs -> Either String CmdArgs
processOutfileArg fn opts = case optOutfile opts of
  Nothing -> Right (opts {optOutfile = Just fn})
  Just _ -> Left "at most one output filename allowed\n"

processInfileArg :: String -> CmdArgs -> Either String CmdArgs
processInfileArg fn opts = case optInfile opts of
  Nothing -> Right (opts {optInfile = Just fn})
  Just _ -> Left "at most one input filename allowed\n"

processArgs :: [String] -> Either String CmdArgs
processArgs argv =
  case getOpt Permute options argv of
    (o, n, []) ->
      foldM (flip processInfileArg) optionsDefault n >>= \ opts' ->
      foldM (flip id) opts' o
    (_, _, errs) ->
      Left (head errs)

putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr

doIf :: Bool -> (a -> Either String a) -> a -> Either String a
doIf True f = f
doIf False f = return

showFile :: Progs -> Either String String
showFile = return . show

alphaRenameProgs :: Substitutable p => (p -> Ctxt) -> p -> Either String p
alphaRenameProgs gf a = return (alphaRename (gf a) a)

processContents :: CmdArgs -> String -> Either String String
processContents (CmdArgs ifn ofn c m e dr l o z) s =
  let e' = e && l
      c' = c && e'
  in
  return s
  -- String to UsProgs
  >>= parse
  -- Pick a unique name for each bound var, needed by infer (and anything else?)
  >>= alphaRenameProgs ctxtAddUsProgs
  -- Add Bool, True, False
  >>= Right . progBuiltins
  -- Type che`ck the file (:: UsProgs -> Progs)
  >>= infer
  >>= if not m then return . show else (\ x -> (Right . monomorphizeFile) x
  >>= Right . argifyFile
--  >>= alphaRenameProgs (const emptyCtxt)
  -- Apply various optimizations
  >>= doIf o optimizeFile
  -- Convert terms from affine to linear
  >>= doIf l affLinFile
  -- Eliminate recursive types (de/refunctionalization)
  >>= doIf e' (elimRecTypes dr)
  -- Apply various optimizations (again) (disabled for now; joinApps problem after aff2lin introduces maybe types)
  >>= doIf o optimizeFile
  -- Pick a unique name for each bound var (again), needed by compileFile
  >>= alphaRenameProgs ctxtAddProgs
  -- Compile to FGG
  >>= if c' then
        \ps -> compileFile ps
               >>= if z then
                     Right . show . sumProduct
                   else
                     Right . showFGG
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
    either die (\ a -> hPutStr ofh a >> exitSuccess) (processContents opts input)    

  Left err ->
    getProgName >>= \ name ->
    putStrLnErr (name ++ ": " ++ err ++ usageInfo ("usage: " ++ name ++ " [OPTION ...] INFILE.ppl") options)
