module Main where
import System.Exit
import Exprs
import Ctxt
import Parse
import Check
import Compile
import Util
import RecType
import Free
import Rename
import AffLin

postprocess :: (Ctxt -> Progs -> a) -> Progs -> a
postprocess f ps = f (ctxtDefProgs ps) ps

-- Parse a file, check and elaborate it, then compile to FGG and output it
main :: IO ()
main =
  getContents >>= \ s ->
  either die (\ a -> print a >> exitSuccess) $
  parseFile s >>=
  return . alphaRenameUsFile >>=
  checkFile >>=
  return . disentangleFile >>= \ (ps, apply_fs) ->
  return (aff2linFile ps) >>=
  return . alphaRenameFile >>=
  return . file2fgg
