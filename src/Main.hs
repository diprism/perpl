module Main where
import System.Exit
import System.Environment
import System.IO
import Exprs
import Parse
import Lex
import TypeInf
import Instantiate
import Compile
import RecType
import AffLin
import Optimize
import Subst
import Ctxt

data CmdArgs = CmdArgs {
  optInfile :: String,
  optOutfile :: String,
  optCompile :: Bool,
  optDerefun :: [(Var, DeRe)],
  optLin :: Bool,
  optOptimize :: Bool
}

optionsDefault = CmdArgs {
  optInfile = "/dev/stdin",
  optOutfile = "/dev/stdout",
  optCompile = True,
  optDerefun = [],
  optLin = True,
  optOptimize = True
}

putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr

help :: IO ()
help =
  getProgName >>= \ name ->
  die (name ++
        " [options] filename.ppl\n" ++
        "Options:\n" ++
        "  -o OUTFILE\tOutput to OUTFILE\n" ++
        "  -O0 -O1\tOptimization level (0 = off, 1 = on, for now)\n" ++
        "  -c\t\tCompile only to PPL code (not to FGG)\n" ++
        "  -l\t\tDon't linearize the file (implies -c)\n" ++
        "  -d DTYPES\tDefunctionalize recursive datatypes DTYPES\n" ++
        "  -r DTYPES\tRefunctionalize recursive datatypes DTYPES")

processArgs' :: CmdArgs -> [String] -> Maybe CmdArgs
processArgs' o ("-o" : fn : as) = processArgs' (o {optOutfile = fn}) as
processArgs' o ("-O0" : as) = processArgs' (o {optOptimize = False}) as
processArgs' o ("-O1" : as) = processArgs' (o {optOptimize = True}) as
processArgs' o ("-c" : as) = processArgs' (o {optCompile = False}) as
processArgs' o ("-l" : as) = processArgs' (o {optLin = False}) as
processArgs' o ("-d" : a : as) =
  processArgs' (o {optDerefun = map (flip (,) Defun) (words a) ++ optDerefun o}) as
processArgs' o ("-r" : a : as) =
  processArgs' (o {optDerefun = map (flip (,) Refun) (words a) ++ optDerefun o}) as
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
--ctxtDefProgs

--process :: Show a => CmdArgs -> String -> a
processContents (CmdArgs ifn ofn c dr l o) s = return s
  -- String to list of tokens
  >>= lexFile
  -- List of tokens to UsProgs
  >>= parseFile
  -- Pick a unique name for each bound var
  >>= alphaRenameProgs ctxtDefUsProgs
  -- Type check the file (:: UsProgs -> Progs)
  >>= inferFile
--  >>= return . show
  >>= Right . instantiateFile
--  >>= alphaRenameProgs (const emptyCtxt)
--  >>= return . show
  -- Apply various optimizations
  >>= doIf o optimizeFile
  -- Eliminate recursive types (de/refunctionalization)
  >>= elimRecTypes dr
--  >>= return . show
  -- Convert terms from affine to linear
  >>= doIf l affLinFile
  -- Apply various optimizations (again) (disabled for now; joinApps problem after aff2lin introduces maybe types)
  >>= doIf o optimizeFile
  -- Pick a unique name for each bound var (again)
  >>= alphaRenameProgs ctxtDefProgs
  -- Compile to FGG
  >>= if c then compileFile else showFile


-- Parse a file, check and elaborate it, then compile to FGG and output it
main :: IO ()
main =
  processArgs >>= either (const help) (\ opts ->
    (openFile (optInfile opts) ReadMode) >>= \ fh ->
     hGetContents fh >>= \ input ->
     either die (\ a -> putStrLn a >> exitSuccess) (processContents opts input))
