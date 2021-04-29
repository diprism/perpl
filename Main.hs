module Main where
import Exprs
import Ctxt
import Parser
import Lexer

--testTerm = "\\? x : bool ->1 bool . x y (observe abc <- \\ y : unit. y y) (if true then false else true)"
--lexedTerm = Lexer.lexStr testTerm
--parsedTerm = lexedTerm >>= Parser.parseTerm

main :: IO ()
main =
  getContents >>= \ s ->
  let lexed = Lexer.lexStr s
      parsed = lexed >>= Parser.parseFile in
  putStrLn (show lexed) >>
  putStrLn (show parsed)
