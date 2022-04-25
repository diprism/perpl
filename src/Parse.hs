module Parse where
import Parse.Parse (parseFile)
import Parse.Lex (lexFile)
import Exprs

parse :: String -> Either String UsProgs
parse contents = lexFile contents >>= parseFile
