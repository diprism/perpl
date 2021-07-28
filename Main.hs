module Main where
import System.Exit
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

--process :: Show a => String -> a
processContents s = return s
  >>= lexFile           -- String to list of tokens
  >>= parseFile         -- List of tokens to UsProgs
  >>= alphaRenameUsFile -- Pick a unique name for each bound var
  >>= checkFile         -- Type check the file
  >>= elimRecTypes      -- Eliminate recursive types (de/refunctionalization)
  >>= aff2linFile       -- Convert terms from affine to linear
  >>= alphaRenameFile   -- Pick a unique name for each bound var (again)
  >>= compileFile       -- Compile to FGG

-- Parse a file, check and elaborate it, then compile to FGG and output it
main :: IO ()
main = getContents >>= either die (\ a -> print a >> exitSuccess) . processContents
