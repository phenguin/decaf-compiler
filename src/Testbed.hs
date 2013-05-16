module Testbed where

import Data.Either
import Varmarker
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.State
import System.IO.Unsafe (unsafePerformIO)
import Scanner
import Control.Monad
import qualified Parser

import PrettyPrint
import ControlFlowGraph
import Codegen
import CFGConstruct 
import CFGConcrete (LGraph, BlockId(..),pprDetailLGraph, pDetail)
import Semantics (SemanticTreeWithSymbols, addSymbolTables)
import Transforms
import Optimization
import ControlFlowGraph (ControlFlowGraph, makeCFG, BranchingStatement, getFunctionParamMap, lgraphSpanningFunctions)
import DataflowAnalysis
import MidIR
import LowIR
import RegisterAlloc

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

testfilepath = "test.dcf"

testMidIr x = fromRight $ midIRFromFile testfilepath
testGlobals x = scrapeGlobals (testMidIr x)
testFunmap x = getFunctionParamMap (testCfgMid' x)
testCfgMid' x = fromRight $ cfgFromFile testfilepath
-- add scoping
testCfgMid x = scopeMidir (testCfgMid' x) (testGlobals x) (testFunmap x)

spillTemp :: Int -> LGraph ProtoASM ProtoBranch -> LGraph ProtoASM ProtoBranch
spillTemp i graph = fst $ runState (flip updateForSpill (VarMarker ("t" ++ show i) Transforms.Single [Temp], BasePtrOffset 1) graph) (0,0)

testCfgLow x = (\(_,x,_) -> x) $ navigate globals funcParamMap $ toLowIRCFG $ (testCfgMid x)
    where midIR = fromRight $ midIRFromFile testfilepath
          cfg = fromRight $ cfgFromFile testfilepath
          globals = scrapeGlobals midIR
          funcParamMap = getFunctionParamMap cfg

