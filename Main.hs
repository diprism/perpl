module Main where
import Exprs
import Ctxt
import Parse
import Lex
import Check
import Compile
import Util
import System.Exit


-- Parse a file, check and elaborate it, then compile to FGG and output it
main :: IO ()
main =
  getContents >>= \ s ->
  maybe2 (Lex.lexStr s >>= Parse.parseFile) (putStrLn "Parse error") $ \ ps ->
  either die (\ a -> a >> exitSuccess) $ checkFile ps >>= \ (g, ps') ->
  Right (putStrLn (show (file2fgg g ps')))
    
