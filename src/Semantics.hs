module Semantics where

import Transforms 
import MultiTree
import Parser (parse)
import Data.Map as M
import Data.Hashable (hash)
import Main (testParse)

data Descriptor = FDesc FDType LitType
                | MDesc LitType [LitType] 
                | PDesc LitType
                | CODesc deriving (Show)

type SemanticTreeWithSymbols = MultiTree (STNode, SymbolTable)
type Scope = M.Map Id Descriptor
type SymbolTable = [Scope]

addSymbolTables :: SemanticTree -> SemanticTreeWithSymbols
addSymbolTables = addSymbolTables' . initSymbols

initSymbols :: SemanticTree -> SemanticTreeWithSymbols
initSymbols = fmap (\x -> (x, []))

removeSymbols :: SemanticTreeWithSymbols -> SemanticTree
removeSymbols = fmap fst

addSymbol :: Id -> Descriptor -> SymbolTable -> SymbolTable
addSymbol i d [] = [M.insert i d $ empty]
addSymbol i d (m:ms) = (M.insert i d m) : ms

addSymbolToScope :: Id -> Descriptor -> Scope -> Scope
addSymbolToScope i d m = M.insert i d m

lookupSymbol :: Id -> SymbolTable -> Maybe Descriptor
lookupSymbol _ [] = Nothing
lookupSymbol k (c:cs) = case M.lookup k c of
    Just x -> Just x
    Nothing -> lookupSymbol k cs

lookupByName :: String -> SymbolTable -> Maybe Descriptor
lookupByName = lookupSymbol . mkId

nameDefined :: String -> SymbolTable -> Bool
nameDefined s st = case lookupByName s st of
    Nothing -> False
    Just _ -> True

getParamTypes :: SemanticTree -> [LitType]
getParamTypes (MT (MD _) ts) = Prelude.map f $ Prelude.filter g ts
    where g (MT (PD _) _) = True
          g _ = False
          f (MT (PD (t, i)) _) = t
          f _ = VoidType -- Hackish

alterScope :: Scope -> SemanticTree -> Scope
alterScope s (MT (FD fdt (t, i)) _) = addSymbolToScope i (FDesc fdt t) s
alterScope s (MT (PD (t, i)) _) = addSymbolToScope i (PDesc t) s
alterScope s (MT (CD i) _) = addSymbolToScope i CODesc s
alterScope s md@(MT (MD (t, i)) _) = addSymbolToScope i (MDesc t (getParamTypes md)) s 
alterScope s _ = s

addNodeDecs :: SemanticTree -> Maybe Scope
addNodeDecs (MT Prog ts) = Just $ Prelude.foldl alterScope empty ts
addNodeDecs (MT DBlock ts) = Just $ Prelude.foldl alterScope empty ts
addNodeDecs (MT (MD _) ts) = Just $ Prelude.foldl alterScope empty ts
addNodeDecs _ = Nothing

addScope :: Scope -> SemanticTreeWithSymbols -> SemanticTreeWithSymbols
addScope s (MT (x, st) ts) = MT (x, s:st) (Prelude.map (addScope s) ts)

addSymbolTables' :: SemanticTreeWithSymbols -> SemanticTreeWithSymbols
addSymbolTables' t@(MT (x, st) ts) = case addNodeDecs (removeSymbols t) of
    Just syms -> MT (x, st) (Prelude.map (addSymbolTables' . addScope syms) ts)
    Nothing -> MT (x, st) (Prelude.map addSymbolTables' ts)

