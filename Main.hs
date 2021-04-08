module Main where
import Parser

testTerm = "\\? x : bool -1> bool . x y (observe abc <- \\ y : unit. y y) (if true then false else true)"
lexedTerm = Parser.lexStr testTerm
parsedTerm = lexedTerm >>= Parser.parseTerm

main :: IO ()
main =
  putStrLn (show lexedTerm) >>
  putStrLn (show parsedTerm)
