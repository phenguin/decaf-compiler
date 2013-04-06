module DataflowAnalysis where

import CFGConcrete
import CFGConstruct
import Control.Monad
import Control.Monad.State
import qualified Data.Map as M

data DataflowResults m l s = DFR (LGraph m l) (M.Map BlockId s) deriving (Eq)

data DFAnalysis m l s = DFAnalysis {
    -- Computes output state of block from input state
    transfer_func :: Block m l -> s -> s,
    -- Combines states
    join_func :: s -> s -> s
    }

runAnalysis :: DFAnalysis m l s -> LGraph m l -> DataflowResults m l s
runAnalysis = undefined
