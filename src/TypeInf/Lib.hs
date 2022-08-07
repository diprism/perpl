module TypeInf.Lib (infer) where
import TypeInf.Solve (inferFile)
import Struct.Lib (UsProgs, SProgs)

infer :: UsProgs -> Either String SProgs
infer = inferFile
