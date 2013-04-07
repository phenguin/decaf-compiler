module Testbed where

import Data.Either
import System.IO.Unsafe (unsafePerformIO)
import Scanner
import Control.Monad
import qualified Parser

import PrettyPrint
import Semantics (SemanticTreeWithSymbols, addSymbolTables)
import Transforms
import Optimization (progIR, Program)
import ControlFlowGraph (ControlFlowGraph, makeCFG)
import DataflowAnalysis

parse :: String -> Either String Parser.Program
parse input = do
    let (errors, tokens) = partitionEithers $ Scanner.scan input
    mapM_ Left errors
    Parser.parse tokens

parseFile :: FilePath -> Either String Parser.Program
parseFile fp = parse (unsafePerformIO $ readFile fp)

semanticTreeFromFile :: FilePath -> Either String SemanticTreeWithSymbols
semanticTreeFromFile fp = do
    parseTree <- parseFile fp
    return $ addSymbolTables (convert parseTree)

midIRFromFile :: FilePath -> Either String Program
midIRFromFile fp = do
    stWithSymbols <- semanticTreeFromFile fp
    return $ progIR stWithSymbols

cfgFromFile :: FilePath -> Either String ControlFlowGraph
cfgFromFile fp = do
    midIR <- midIRFromFile fp
    return $ makeCFG midIR

