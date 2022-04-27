module Parse.Lib (parse) where
import Parse.Parse (parseFile)
import Parse.Lex (lexFile)
import Struct.Lib

parse :: String -> Either String UsProgs
parse contents = lexFile contents >>= parseFile
