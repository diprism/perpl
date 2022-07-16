{- JSON Functions -}

module Util.JSON where
import Data.List (intercalate)

data JSON =
    JSnull
  | JSbool Bool
  | JSint Int
  | JSdouble Double
  | JSstring String
  | JSarray [JSON]
  | JSobject [(String, JSON)]

instance Show JSON where
  show JSnull = "null"
  show (JSbool b) = if b then "true" else "false"
  show (JSint i) = show i
  show (JSdouble d) = show d
  show (JSstring s) = show s
  show (JSarray js) = '[' : intercalate "," [show a | a <- js] ++ "]"
  show (JSobject kvs) = '{' : intercalate "," [show k ++ ":" ++ show v | (k, v) <- kvs] ++ "}"

pprint_json :: JSON -> String
pprint_json j = pp j 0 where
  indent i = '\n' : replicate i ' '
  pp (JSarray js) i = "[" ++ intercalate "," [indent (i+2) ++ pp j (i+2) | j <- js] ++ indent i ++ "]"
  pp (JSobject kvs) i = "{" ++ intercalate "," [indent (i+2) ++ show k ++ ": " ++ pp v (i+2) | (k, v) <- kvs] ++ indent i ++ "}"
  pp j i = show j
