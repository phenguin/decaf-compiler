module Semantics where

import Transforms 
import Parser (parse)
import Data.Map as M
import Data.Hashable (hash)


data Descriptor = FDesc LitType
                | MDesc LitType [LitType] LitType
                | CODesc deriving (Show)

type SymbolTable = [M.Map Id Descriptor]

addSymbol :: Id -> Descriptor -> SymbolTable -> SymbolTable
addSymbol i d [] = [M.insert i d $ empty]
addSymbol i d (m:ms) = (M.insert i d m) : ms

lookupSymbol :: Id -> SymbolTable -> Maybe Descriptor
lookupSymbol _ [] = Nothing
lookupSymbol k (c:cs) = case M.lookup k c of
    Just x -> Just x
    Nothing -> lookupSymbol k cs

lookupByName :: String -> SymbolTable -> Maybe Descriptor
lookupByName = lookupSymbol . mkId

