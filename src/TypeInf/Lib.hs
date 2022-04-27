module TypeInf.Lib (infer) where
import TypeInf.Solve (inferFile)
import Struct.Lib

infer :: UsProgs -> Either String SProgs
infer = inferFile
