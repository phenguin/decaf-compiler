module DataflowAnalysis where

import CFGConcrete
import Data.List (foldl1)
import Control.Applicative
import PrettyPrint
import CFGConstruct
import Control.Monad
import Control.Monad.State
import Data.Maybe (isJust, fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as M

data DataflowResults m l s = DFR (LGraph m l) (M.Map BlockId s) deriving (Eq)

data DFAnalysis m l s = DFAnalysis {
    -- Computes output state of block from input state
    transfer_func :: Block m l -> s -> s,
    -- Combines states
    join_func :: s -> s -> s,
    initState :: s
    }

stepAnalysis :: (Eq s, PrettyPrint m, PrettyPrint l, LastNode l) => 
    DFAnalysis m l s -> BlockLookup m l -> M.Map BlockId s -> BlockId -> State (Set BlockId) (M.Map BlockId s)

stepAnalysis (DFAnalysis trans join initState) bLookup res bid = do
    let block = case lookupBlock bid bLookup of
           Nothing -> error "Cant find block"
           Just b -> b
        f predBid = case M.lookup predBid res of
           Nothing -> initState
           Just x -> x
        g (Block bid _) = f bid
        predecessors = predsOfBlock bLookup bid
        predsWithStates = map ((,) <$> id <*> g) predecessors
        oldInState = f bid
        bInState = foldl join initState $ map (uncurry trans) predsWithStates
    modify (Set.delete bid)
    when (bInState /= oldInState) $ modify (Set.union (Set.fromList $ succs block))
    return $ M.insert bid bInState res

-- Terminates if fixed point for analysis found
doAnalysis :: (Eq s, PrettyPrint l, PrettyPrint m, LastNode l) => 
    DFAnalysis m l s -> BlockLookup m l -> M.Map BlockId s -> [Block m l] -> M.Map BlockId s
doAnalysis analysis bLookup startStates blocks =
    case Set.null workSet of
        True -> res
        False -> doAnalysis analysis bLookup res $ 
                 map fromJust $ filter isJust $ 
                 map ((flip lookupBlock) bLookup) $
                 (Set.toList workSet)
  where fm = stepAnalysis analysis bLookup
        (res, workSet) = runState partialResult Set.empty
        partialResult = foldM fm startStates $ map getBID blocks
        getBID (Block bid _) = bid
        
