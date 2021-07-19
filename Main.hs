module Main where
import Exprs
import Ctxt
import Parse
import Check
import Compile
import Util
import System.Exit


-- Parse a file, check and elaborate it, then compile to FGG and output it
main :: IO ()
main =
  getContents >>= \ s ->
  either die (\ a -> print a >> exitSuccess) $
  Parse.parseFile s >>= \ ps ->
  checkFile ps >>= \ (g, ps') ->
  return (file2fgg g ps')
