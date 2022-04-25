module TypeInf.Lib (infer) where
import TypeInf.Solve (inferFile)
import Exprs

infer :: UsProgs -> Either String SProgs
infer = inferFile
