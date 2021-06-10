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
  let lexed = Lex.lexStr s
      parsed = lexed >>= Parse.parseFile in
    maybe2 parsed (putStrLn "Parse error") $ \ ps ->
    either die (\ a -> a >> exitSuccess) $ checkFile ps >>= \ ps' ->
    Right $ putStrLn $ show $ file2fgg ps'
    
