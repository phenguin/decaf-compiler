module Optimization where

import DataflowAnalysis
import Debug.Trace (trace)
import Data.Data
import Data.Typeable
import Data.Generics
import Configuration
import Configuration.Types
import MidIR
import LowIR
import Util
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

type Opt m l = LGraph m l -> LGraph m l

-- Cause an optimization to keep running until it reaches a fixed point on the CFG in question
untilStable :: (Eq m, Eq l) => Opt m l -> Opt m l
untilStable opt lgraph = if lgraph' `deepEq` lgraph then lgraph' else (untilStable opt) lgraph'
    where lgraph' = opt lgraph

runOpt :: (Eq s, PrettyPrint s, PrettyPrint l, PrettyPrint m, LastNode l) => 
    Optimization m l s -> LGraph m l -> LGraph m l

runOpt (Opt dfa@(DFAnalysis updateM updateL _ _ Forward) mTrans lTrans) lg@(LGraph entryId bLookup) = LGraph entryId bLookup'
    where DFR _ sLookup = runAnalysis dfa lg
          bLookup' = M.map mapping_f bLookup

          mapping_f blk@(Block bid zt) = case maybeInS of
                                      Nothing -> blk
                                      Just s -> Block bid $ ztailFromMiddles (mids ++ mids') zlast
            where maybeInS = M.lookup bid sLookup
                  -- Dont use fromJust here.. temporary for now
                  blkMids = blockMiddles blk
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

runOpt (Opt dfa@(DFAnalysis updateM updateL _ _ Backward) mTrans lTrans) lg@(LGraph entryId bLookup) = LGraph entryId bLookup'
    where DFR _ sLookup = runAnalysis dfa lg
          bLookup' = M.map mapping_f bLookup

          mapping_f blk@(Block bid zt) = case maybeOutS of
                                      Nothing -> blk
                                      Just s -> Block bid $ ztailFromMiddles (mids ++ mids') zlast
            where maybeOutS = M.lookup bid sLookup
                  -- Dont use fromJust here.. temporary for now
                  blkMids = reverse (blockMiddles blk)
                  (mids, _) = runState (foldM foldF [] blkMids) outS'
                  outS = fromJust maybeOutS
                  outS' = case getZLast blk of
                      LastExit -> outS
                      LastOther l -> updateL l outS
                  (mids', zlast) = lTrans outS outS' $ getZLast blk
                  foldF acc m = do
                      s <- get
                      let s' = updateM m s
                      put s'
                      return $ (mTrans s s' m) ++ acc
-- Global Common Subexpression Elimination

globalCSE :: Optimization Statement BranchingStatement AvailExprState
globalCSE = Opt availableExprAnalysis globalCSEmTrans globalCSElTrans

optGlobalCSE :: LGraph Statement BranchingStatement -> LGraph Statement BranchingStatement
optGlobalCSE = runOpt globalCSE

mkExprTemp :: Expression -> Variable
mkExprTemp e = Scopedvar [Temp] (Var $ "temp_for_" ++ filter (/= ' ') (pPrint e) ++ "_")

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

---------------------------------
-- Dead Code Elimination         
---------------------------------

-- for MidIR

midIrDeadCodeElimination :: Optimization Statement BranchingStatement LiveVarState
midIrDeadCodeElimination = Opt liveVariableAnalysis deadcodeMTransMid deadcodeLTransMid

optMidIrDeadCodeElim :: LGraph Statement BranchingStatement -> LGraph Statement BranchingStatement
optMidIrDeadCodeElim = runOpt midIrDeadCodeElimination

deadcodeMTransMid :: LiveVarState -> LiveVarState -> Statement -> [Statement]
-- in / out flipped because analysis runs backwards
deadcodeMTransMid outState inState stmt@(Set var expr) = case (vm `Set.member` outState) || isFuncCall expr of
        True -> [stmt]
        False -> []
    where vm = varToVarMarker var
          isFuncCall (FuncCall _ _) = True
          isFuncCall _ = False
deadcodeMTransMid _ _ stmt = [stmt]

deadcodeLTransMid :: LiveVarState -> LiveVarState -> ZLast BranchingStatement -> ([Statement], ZLast BranchingStatement)
deadcodeLTransMid outState inState zl = ([], zl)

-- for LowIR
--
lowIrDeadCodeElimination :: Optimization ProtoASM ProtoBranch LiveVarState
lowIrDeadCodeElimination = Opt lowLVAnalysis deadcodeMTransLow deadcodeLTransLow

optLowIrDeadCodeElim :: LGraph ProtoASM ProtoBranch -> LGraph ProtoASM ProtoBranch
optLowIrDeadCodeElim = runOpt lowIrDeadCodeElimination

deadcodeMTransLow :: LiveVarState -> LiveVarState -> ProtoASM -> [ProtoASM]
-- in / out flipped because analysis runs backwards
deadcodeMTransLow outState inState asm = case asm of
        Mov' _ v -> answer v
        Neg' v   -> answer v
        And' _ v -> answer v
        Or' _ v  -> answer v
        Add' _ v -> answer v
        Sub' v _ -> answer v
        Mul' _ v -> answer v
        Div' v   -> [asm] -- TODO: Come back
        Not' v   -> answer v
        Pop' v   -> answer v
        _ -> [asm]
    where maybeVM v = case Set.toList $ valToVMSet v of
              [x] -> Just x
              _ -> Nothing
          output vm = case vm `Set.member` outState of
                True -> [asm]
                False -> []
          answer v = case liftM output $ maybeVM v of
                Just ans -> ans
                Nothing -> [asm]

deadcodeLTransLow :: LiveVarState -> LiveVarState -> ZLast ProtoBranch -> ([ProtoASM], ZLast ProtoBranch)
deadcodeLTransLow outState inState zl = ([], zl)
