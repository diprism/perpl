module Main where
import System.Exit
import System.Environment
import System.IO
import Exprs
import Ctxt
import Parse
import Lex
import Check
import Compile
import Util
import RecType
import Free
import Rename
import AffLin
import Optimize

data Options = Options {
  optCompile :: Bool,
  optDefun :: Bool,
  optRefun :: Bool,
  optLin :: Bool,
  optAlpha :: Bool,
  optOptimize :: Bool
}

optionsDefault = Options True True True True True True

putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr

help :: IO String
help = getProgName >>= \ name -> return $
  name ++ " [option] < filename.ppl\n" ++
  "Options:\n" ++
  " -c Y/N, --compile=Y/N            Compile to FGG (default)\n" ++
  " -d Y/N, --defunctionalize=Y/N    Defunctionalize recursive datatypes\n" ++
  " -r Y/N, --refunctionalize=Y/N    Refunctionalize recursive datatypes\n" ++
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
processArgs'' a yn o = processYN yn >>= h a o where
  h arg (Options c d r l a o) yn
    | arg `elem` ["-c", "--compile"]         = Just (Options yn d r l a o)
    | arg `elem` ["-d", "--defunctionalize"] = Just (Options c yn r l a o)
    | arg `elem` ["-r", "--refunctionalize"] = Just (Options c d yn l a o)
    | arg `elem` ["-l", "--linearize"]       = Just (Options c d r yn a o)
    | arg `elem` ["-a", "--alpha"]           = Just (Options c d r l yn o)
    | arg `elem` ["-o", "--optimize"]        = Just (Options c d r l a yn)
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
processContents (Options c d r l a o) s = return s
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
  -- TODO: d and r
  >>= doIf d elimRecTypes
  -- Convert terms from affine to linear
  >>= doIf l aff2linFile
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
