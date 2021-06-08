module Main where
import Exprs
import Ctxt
import Parser
import Lexer
import Check
import Compile
import System.Exit

--testTerm = "\\? x : bool ->1 bool . x y (observe abc <- \\ y : unit. y y) (if true then false else true)"
--lexedTerm = Lexer.lexStr testTerm
--parsedTerm = lexedTerm >>= Parser.parseTerm

main :: IO ()
main =
  getContents >>= \ s ->
  let lexed = Lexer.lexStr s
      parsed = lexed >>= Parser.parseFile in
    --putStrLn (show lexed) >>
    --putStrLn (show parsed) >>= \ _ -> -- (>>) won't parse with ($)
    maybe2 parsed (putStrLn "Parse error") $ \ ps ->
    either die (\ a -> a >> exitSuccess) $ checkFile ps >>= \ ps' ->
    Right $ putStrLn $ show $ file2fgg ps'
    
