module Testbed where

import Data.Either
import System.IO.Unsafe (unsafePerformIO)
import Scanner
import Control.Monad
import qualified Parser

import PrettyPrint
import CFGConstruct (lgraphFromAGraphBlocks)
import CFGConcrete (LGraph, BlockId(..))
import Semantics (SemanticTreeWithSymbols, addSymbolTables)
import Transforms
import Optimization
import ControlFlowGraph (ControlFlowGraph, makeCFG, BranchingStatement, getFunctionParamMap, lgraphSpanningFunctions)
import DataflowAnalysis
import MidIR

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

cfgFromFile :: FilePath -> Either String (LGraph Statement BranchingStatement)
cfgFromFile fp = do
    midIR <- midIRFromFile fp
    return $ lgraphSpanningFunctions (makeCFG midIR)

pPrintE :: (PrettyPrint a) => Either String a -> IO ()
pPrintE (Left s) = putStrLn s
pPrintE (Right x) = putStrLn $ pPrint x

