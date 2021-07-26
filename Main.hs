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
processContents s =
  lexFile s         >>=
  parseFile         >>=
  alphaRenameUsFile >>=
  checkFile         >>=
  disentangleFile   >>=
  elimRecTypes      >>=
  aff2linFile       >>=
  alphaRenameFile   >>=
  compileFile

-- Parse a file, check and elaborate it, then compile to FGG and output it
main :: IO ()
main = getContents >>= either die (\ a -> print a >> exitSuccess) . processContents
