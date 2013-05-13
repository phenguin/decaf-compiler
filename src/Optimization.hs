module Optimization where

import DataflowAnalysis
import Debug.Trace (trace)
import Data.Data
import Data.Typeable
import Data.Generics
import Configuration
import Configuration.Types
import MidIR
import ControlFlowGraph
import Data.Maybe
import Control.Monad.State
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as M
import CFGConcrete
import CFGConstruct
import PrettyPrint

data Optimization m l s = Opt {
    dfa :: DFAnalysis m l s,
    
    -- Takes the in state of a middle node, the out state of a middle node, and the node, and gives a set of nodes to replace with
    mTransform :: s -> s -> m -> [m],
    
    -- takes the instate of a last node and the last node, and outputs middles to prepend it with together with a new last node
    -- currently, the last nodes do not update the state in any way so we don't need an out state but this may change
    lTransform :: s -> s -> ZLast l -> ([m], ZLast l)
    }

runOpt :: (Eq s, PrettyPrint s, PrettyPrint l, PrettyPrint m, LastNode l) => 
    Optimization m l s -> LGraph m l -> LGraph m l

runOpt (Opt dfa@(DFAnalysis updateM updateL _ _ dir) mTrans lTrans) lg@(LGraph entryId bLookup) = LGraph entryId bLookup'
    where DFR _ sLookup = runAnalysis dfa lg
          bLookup' = M.map mapping_f bLookup

          mapping_f blk@(Block bid zt) = case maybeInS of
                                      Nothing -> blk
                                      Just s -> Block bid $ ztailFromMiddles (mids ++ mids') zlast
            where maybeInS = M.lookup bid sLookup
                  -- Dont use fromJust here.. temporary for now
                  blkMids = if dir == Forward then blockMiddles blk else reverse (blockMiddles blk)
                  (mids, outS) = runState (foldM foldF [] blkMids) (fromJust maybeInS)
                  outS' = case getZLast blk of
                      LastExit -> outS
                      LastOther l -> updateL l outS
                  (mids', zlast) = lTrans outS outS' $ getZLast blk
                  foldF acc m = do
                      s <- get
                      let s' = updateM m s
                      put s'
                      return $ acc ++ (mTrans s s' m)

-- Global Common Subexpression Elimination

globalCSE :: Optimization Statement BranchingStatement AvailExprState
globalCSE = Opt availableExprAnalysis globalCSEmTrans globalCSElTrans

mkExprTemp :: Expression -> Variable
mkExprTemp e = Var $ "temp_for_" ++ filter (/= ' ') (pPrint e) ++ "_"

globalCSEmTrans :: AvailExprState -> AvailExprState -> Statement -> [Statement]

globalCSEmTrans inState outState st@(Set v expr) = tempAssigns ++ [Set v $ subAvailExprs outState expr]
    where tempAssigns = map (\e -> (Set (mkExprTemp e) e)) $ filter (not . ((flip Set.member) inState)) $ subexpressions expr
          mapF e = Set (mkExprTemp e) (subAvailExprs inState e)

globalCSEmTrans inState _ st@(Return expr) = [Return $ subAvailExprs inState expr]
globalCSEmTrans inState _ st@(Callout name params) = [Callout name $ map (subAvailExprs inState) params]
globalCSEmTrans inState _ st@(Function name params) = [Function name $ map (subAvailExprs inState) params]
globalCSEmTrans _ _ st = [st]

globalCSElTrans :: AvailExprState -> AvailExprState -> ZLast BranchingStatement -> ([Statement], ZLast BranchingStatement)

globalCSElTrans inState outState (LastOther (IfBranch expr bid bid')) = ([], l')
    where l' = LastOther $ IfBranch (subAvailExprs inState expr) bid bid'

globalCSElTrans inState outState (LastOther (WhileBranch expr bid bid')) = ([], l')
    where l' = LastOther $ WhileBranch (subAvailExprs inState expr) bid bid'

globalCSElTrans _ _ l = ([], l)

-- Top-down attempt to substitute expressions with precomputed values.. using generic programming to simplify code alot.. see scrap your boilerplate
subAvailExprs :: AvailExprState -> Expression -> Expression
subAvailExprs exprs expr = everywhere' (mkT (tryExprSub exprs)) expr

tryExprSub :: AvailExprState -> Expression -> Expression
tryExprSub exprs expr 
    | canSub expr = doSub expr
    | otherwise = expr
   where canSub expr = Set.member expr exprs
         doSub expr = Loc $ mkExprTemp expr


