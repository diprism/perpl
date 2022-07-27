module Main where
import System.Exit
import System.Environment
import System.IO
import Struct.Lib
import Parse.Lib
import TypeInf.Lib
import Compile.Lib
import Transform.Monomorphize
import Transform.DR
import Transform.AffLin
import Transform.Optimize
import Transform.Argify
import Scope.Subst
import Scope.Ctxt
import Util.FGG
import Util.SumProduct

data CmdArgs = CmdArgs {
  optInfile :: String,
  optOutfile :: String,
  optCompile :: Bool,
  optMono :: Bool,
  optElimRecs :: Bool,
  optDerefun :: [(Var, DeRe)],
  optLin :: Bool,
  optOptimize :: Bool,
  optSumProduct :: Bool
}

optionsDefault = CmdArgs {
  optInfile = "/dev/stdin",
  optOutfile = "/dev/stdout",
  optCompile = True,
  optMono = True,
  optElimRecs = True,
  optDerefun = [],
  optLin = True,
  optOptimize = True,
  optSumProduct = False
}

putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr

help :: IO ()
help =
  getProgName >>= \ name ->
  die (name ++
        " [options] filename.ppl\n" ++
        "Options:\n" ++
        "  -o OUTFILE  Output to OUTFILE\n" ++
        "  -O0 -O1     Optimization level (0 = off, 1 = on, for now)\n" ++
        "  -c          Compile only to PPL code (not to FGG)\n" ++
        "  -e          Don't eliminate recursive datatypes (implies -c)\n" ++
        "  -m          Don't monomorphize (implies -e)\n" ++
        "  -l          Don't linearize the file (implies -e)\n" ++
        "  -d DTYPES   Defunctionalize recursive datatypes DTYPES\n" ++
        "  -r DTYPES   Refunctionalize recursive datatypes DTYPES\n" ++
        "  -z          Compute sum-product")
        

processArgs' :: CmdArgs -> [String] -> Maybe CmdArgs
processArgs' o ("-o" : fn : as) = processArgs' (o {optOutfile = fn}) as
processArgs' o ("-O0" : as) = processArgs' (o {optOptimize = False}) as
processArgs' o ("-O1" : as) = processArgs' (o {optOptimize = True}) as
processArgs' o ("-c" : as) = processArgs' (o {optCompile = False}) as
processArgs' o ("-m" : as) = processArgs' (o {optMono = False}) as
processArgs' o ("-e" : as) = processArgs' (o {optElimRecs = False}) as
processArgs' o ("-l" : as) = processArgs' (o {optLin = False}) as
processArgs' o ("-d" : a : as) =
  processArgs' (o {optDerefun = map (flip (,) Defun) (words a) ++ optDerefun o}) as
processArgs' o ("-r" : a : as) =
  processArgs' (o {optDerefun = map (flip (,) Refun) (words a) ++ optDerefun o}) as
processArgs' o ("-z" : as) = processArgs' (o {optSumProduct = True}) as  
processArgs' o (('-' : _) : _) = Nothing
processArgs' o (fn : as) = processArgs' (o {optInfile = fn}) as
processArgs' o [] = Just o

processArgs :: IO (Either () CmdArgs)
processArgs =
  maybe (Left ()) Right <$> processArgs' optionsDefault <$> getArgs

doIf :: Bool -> (a -> Either String a) -> a -> Either String a
doIf True f = f
doIf False f = return

showFile :: Progs -> Either String String
showFile = return . show

alphaRenameProgs :: Substitutable p => (p -> Ctxt) -> p -> Either String p
alphaRenameProgs gf a = return (alphaRename (gf a) a)

processContents :: CmdArgs -> String -> Either String String
processContents (CmdArgs ifn ofn c m e dr l o z) s =
  let e' = e && m && l
      c' = c && e
  in
  return s
  -- String to UsProgs
  >>= parse
  -- Pick a unique name for each bound var
  >>= alphaRenameProgs ctxtDefUsProgs
  -- Add Bool, True, False
  >>= Right . progBuiltins
  -- Type check the file (:: UsProgs -> Progs)
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
  -- Pick a unique name for each bound var (again)
  >>= alphaRenameProgs ctxtDefProgs
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
main =
  processArgs >>= either (const help) (\ opts ->
    (openFile (optInfile opts) ReadMode) >>= \ fh ->
     hGetContents fh >>= \ input ->
     either die (\ a -> writeFile (optOutfile opts) a >> exitSuccess) (processContents opts input))
