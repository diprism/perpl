module Main where
import System.Exit
import System.Environment
import System.IO
import Exprs
import Parse
import Lex
import Check
import Compile
import Util
import RecType
import Rename
import AffLin
import Optimize

data Options = Options {
  optCompile :: Bool,
  optDerefun :: [(Var, DeRe)],
  optLin :: Bool,
  optAlpha :: Bool,
  optOptimize :: Bool
}

optionsDefault = Options True [] True True True

putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr

help :: IO String
help = getProgName >>= \ name -> return $
  name ++ " [option] < filename.ppl\n" ++
  "Options:\n" ++
  " -c Y/N, --compile=Y/N            Compile to FGG (default)\n" ++
  " -d VAR, --defunctionalize=VAR    Defunctionalize recursive datatype VAR\n" ++
  " -r VAR, --refunctionalize=VAR    Refunctionalize recursive datatype VAR\n" ++
  " -l Y/N, --linearize=Y/N          Linearize the file (from affine)\n" ++
  " -a Y/N, --alpha=Y/N              Alpha-rename\n" ++
  " -o Y/N, --optimize=Y/N           Apply optimizations"

noStrings  = ["no",  "No",  "NO",  "N", "n", "0", "false", "False", "FALSE", "F", "f", "off", "Off", "OFF"]
yesStrings = ["yes", "Yes", "YES", "Y", "y", "1", "true",  "True",  "TRUE",  "T", "t", "on",  "On",  "ON" ]
processYN :: String -> Maybe Bool
processYN s
  | s `elem` noStrings  = Just False
  | s `elem` yesStrings = Just True
  | otherwise = Nothing

isLongArg :: String -> Maybe (String, String)
isLongArg "" = Nothing
isLongArg ('=' : s) = Just ("", s)
isLongArg (c : s) = fmap (\ (a, yn) -> (c : a, yn)) (isLongArg s)

processArgs'' :: String -> String -> Options -> Maybe Options
processArgs'' a val o = h a o where
  h arg (Options c dr l a o)
    | arg `elem` ["-c", "--compile"] =
        processYN val >>= \ yn -> Just (Options yn dr l a o)
    | arg `elem` ["-d", "--defunctionalize"] =
        Just (Options c (dr ++ [(val, Defun)]) l a o)
    | arg `elem` ["-r", "--refunctionalize"] =
        Just (Options c (dr ++ [(val, Refun)]) l a o)
    | arg `elem` ["-l", "--linearize"] =
        processYN val >>= \ yn -> Just (Options c dr yn a o)
    | arg `elem` ["-a", "--alpha"] =
        processYN val >>= \ yn -> Just (Options c dr l yn o)
    | arg `elem` ["-o", "--optimize"] =
        processYN val >>= \ yn -> Just (Options c dr l a yn)
    | otherwise = Nothing

processArgs' :: Options -> [String] -> Maybe Options
processArgs' o [] = Just o
processArgs' o (a : []) = isLongArg a >>= \ (a, yn) -> processArgs'' a yn o
processArgs' o (a : a' : as) =
  maybe
    (processArgs'' a a' o >>= \ o -> processArgs' o as)
    (\ (a, yn) -> processArgs'' a yn o >>= \ o -> processArgs' o (a' : as))
    (isLongArg a)

processArgs :: IO (Either () Options)
processArgs = getArgs >>= return . maybe (Left ()) Right . processArgs' optionsDefault


doIf :: Bool -> (a -> Either String a) -> a -> Either String a
doIf True f = f
doIf False f = return

showFile :: Progs -> Either String String
showFile = return . show

--process :: Show a => Options -> String -> a
processContents (Options c dr l a o) s = return s
  -- String to list of tokens
  >>= lexFile
  -- List of tokens to UsProgs
  >>= parseFile
  -- Pick a unique name for each bound var
  >>= doIf a alphaRenameUsFile
  -- Type check the file (:: UsProgs -> Progs)
  >>= checkFile
  -- Apply various optimizations
  >>= doIf o optimizeFile
  -- Eliminate recursive types (de/refunctionalization)
  >>= elimRecTypes dr
  -- Convert terms from affine to linear
  >>= doIf l affLinFile
  -- Apply various optimizations (again) (disabled for now; joinApps problem after aff2lin introduces maybe types)
  >>= doIf o optimizeFile
  -- Pick a unique name for each bound var (again)
  >>= doIf a alphaRenameFile
  -- Compile to FGG
  >>= if c then compileFile else showFile

-- Parse a file, check and elaborate it, then compile to FGG and output it
main :: IO ()
main =
  processArgs >>= \ mopts ->
  getContents >>= \ input ->
  either (\ e -> e >>= die) (\ a -> putStrLn a >> exitSuccess)
    (mapLeft (const help) mopts >>= \ opts -> mapLeft return (processContents opts input))
