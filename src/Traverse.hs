module Traverse where

import Data.Maybe
import Prelude
import Transforms
import MultiTree
import Main
import qualified Data.IORef 
import qualified Data.HashMap.Strict as H
import System.IO.Unsafe
import Control.Monad.State

expand:: SemanticTree -> [SemanticTree]
expand (MT _ a) = a
expand _ = [] 

traverse f tree = case (f tree) of 
                Just b -> b
                Nothing -> and $ map (traverse f) (expand tree)

arrDecCheck (MT (FD (Array n) _) [])  = Just $ n> 0
arrDecCheck  _ = Nothing
checkArrayDeclarationNotZero p = traverse arrDecCheck p


