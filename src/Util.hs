module Util where

import System.IO.Unsafe (unsafePerformIO)

import Transforms (SemanticTree, convert)
import Data.Hashable (Hashable, hash)
import MultiTree (pPrintTabbed)
import PrettyPrint
import qualified Parser
import Data.Either
import Configuration (Configuration, CompilerStage(..), OptimizationSpecification(..))
import qualified Configuration
import qualified Scanner
import Configuration.Types

{- Since our compiler only handles single files, the 'Configuration' struct
doesn't currently get passed through to the scanner and parser code.  (This may
change--one can see the scanner and parser as acting in a reader monad.)  The
big problem with this is that error messages generated in the scanner and
parser won't contain the file name--the file name has to get added in this
function. -}
mungeErrorMessage :: Configuration -> Either String a -> Either String a
mungeErrorMessage configuration =
  ifLeft ((Configuration.input configuration ++ " ")++)
  where ifLeft f (Left v) = Left $ f v
        ifLeft _ (Right a) = Right a

-- Use unsafe perform io to get a "ghci friendly" parse tree for debugging
ghciparse :: Configuration -> String -> Either String Parser.Program
ghciparse configuration input = do
  let (errors, tokens) = partitionEithers $ Scanner.scan input
  -- If errors occurred, bail out.
  mapM_ (mungeErrorMessage configuration . Left) errors
  -- Otherwise, attempt a parse.
  mungeErrorMessage configuration $ Parser.parse tokens


testParse :: FilePath -> Either String Parser.Program
testParse fp = ghciparse (Configuration.testConfiguration fp) input
    where input = unsafePerformIO $ Prelude.readFile fp

prettyIRTree :: (SemanticTree -> String) -> FilePath -> String
prettyIRTree f fp = case testParse fp of
    Left err -> err
    Right program -> f $ convert program

putIRTreeTabbed :: FilePath -> IO ()
putIRTreeTabbed = putStrLn . prettyIRTree pPrintTabbed

putIRTree :: FilePath -> IO ()
putIRTree = putStrLn . prettyIRTree pPrint

getHashStr :: (Hashable a) => a -> String
getHashStr x = case h < 0 of
    True -> 'N' : show (abs h)
    False -> 'P' : show h
    where h = hash x

