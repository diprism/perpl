module TypeInf.Lib (infer, desugar) where
import TypeInf.Solve (inferFile)
import TypeInf.Desugar (desugarFile)
import Struct.Lib (UsProgs, SProgs)

infer :: UsProgs -> Either String SProgs
infer = inferFile

desugar :: UsProgs -> Either String UsProgs
desugar = desugarFile