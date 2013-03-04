module Traverse where

import Data.Maybe
import Prelude
import Transforms
import MultiTree
import Main
import Semantics
import qualified Data.IORef 
import qualified Data.HashMap.Strict as H
import System.IO.Unsafe
import Control.Monad.State

expand:: SemanticTreeWithSymbols -> [SemanticTreeWithSymbols]
expand (MT _ a) = a

type Error = Maybe String
data TraverseControl = Up Error | Down Error
traverse:: (SemanticTreeWithSymbols -> TraverseControl) -> SemanticTreeWithSymbols -> [Error]
traverse f tree = case (f tree) of 
                Up error -> [error]
                Down error -> filter isJust $ error:(foldr (++) [] $ map (traverse f) (expand tree))

