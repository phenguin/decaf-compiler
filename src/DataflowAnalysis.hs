{-# LANGUAGE DeriveDataTypeable #-}
module DataflowAnalysis where

import CFGConcrete
import Varmarker
import Util
import LowIR
import Data.Typeable
import Data.Data
import qualified Transforms
import Debug.Trace (trace)
import Data.List (foldl1)
import Control.Applicative
import PrettyPrint
import CFGConstruct
import Control.Monad
import Control.Monad.State
import Data.Maybe (catMaybes, isJust, fromJust)
import qualified Data.Set as Set
import Data.Set (Set)
import MidIR 
import MonadUniqueEnv
import qualified Data.Set as Set
import qualified Data.Map as M
import Data.Map ((!))
import Text.PrettyPrint.HughesPJ
import Data.Generics
import ControlFlowGraph

data DataflowResults m l s = DFR (LGraph m l) (M.Map BlockId s) deriving (Eq)

instance (PrettyPrint s, PrettyPrint m, PrettyPrint l, LastNode l) => PrettyPrint (DataflowResults m l s) where
    ppr (DFR lgraph resMap) = foldl f (text "") dfsBlocks
        where dfsBlocks = postorderDFS lgraph
              f doc blk@(Block bid _) = case M.lookup bid resMap of
                  Nothing -> doc $$ ppr blk
                  Just x -> doc $$ text "" $$
                            lbrack <+> ppr x <+> rbrack $$
                            ppr blk

data DFDirection = Backward | Forward deriving (Show, Eq, Ord)

data DFAnalysis m l s = DFAnalysis {
    -- Computes output state of block from input state
    -- maybe need to add update state for last node?
    updateStateM :: m -> s -> s,
    updateStateL :: l -> s -> s,
    -- Combines states
    joinStates :: s -> s -> s,
    initState :: s,
    direction :: DFDirection
    }

computeTransferFunc :: (LastNode l) =>
    DFAnalysis m l s -> Block m l -> s -> s

computeTransferFunc (DFAnalysis updateM updateL _ _ Forward) block inState = case getZLast block of
    LastExit -> resultOfMids
    LastOther l -> updateL l resultOfMids
  where resultOfMids = foldl (flip updateM) inState $ blockMiddles block

computeTransferFunc (DFAnalysis updateM updateL _ _ Backward) block inState = foldl (flip updateM) inState' $ reverse (blockMiddles block)
    where inState' = case getZLast block of
            LastExit -> inState
            LastOther l -> updateL l inState

stepAnalysis :: (Eq s, LastNode l) => 
    DFAnalysis m l s -> BlockLookup m l -> M.Map BlockId s -> BlockId -> State (Set BlockId) (M.Map BlockId s)

stepAnalysis dfa@(DFAnalysis updateM updateL join initState Forward) bLookup res bid = do
    let block = case lookupBlock bid bLookup of
           Nothing -> error "Cant find block"
           Just b -> b
        f predBid = M.lookup predBid res
        g (Block bid _) = f bid
        predecessors = predsOfBlock bLookup bid
        trans = computeTransferFunc dfa
        predsWithStates = zip predecessors (catMaybes $ map g predecessors)
        predsWithOutStates = map (\(b@(Block leId _), s) -> (b, s, trans b s)) predsWithStates

        bInState = let predStates = map (uncurry trans) predsWithStates in
                       case predStates of
                           [] -> initState
                           xs -> foldl1 join xs

        oldInState = f bid
    modify (Set.delete bid)
    when ((Just bInState) /= oldInState) $ modify (Set.union (Set.fromList $ succs block))
    return $ M.insert bid bInState res

stepAnalysis dfa@(DFAnalysis updateM updateL join initState Backward) bLookup res bid = do
    let block = case lookupBlock bid bLookup of
           Nothing -> error "Cant find block"
           Just b -> b
        f succBid = M.lookup succBid res
        g (Block bid _) = f bid
        successors = succsOfBlock bLookup bid
        trans = computeTransferFunc dfa
        succsWithStates = zip successors (catMaybes $ map g successors)
        succsWithOutStates = map (\(b@(Block leId _), s) -> (b, s, trans b s)) succsWithStates

        bInState = let succStates = map (uncurry trans) succsWithStates in
                       case succStates of
                           [] -> initState
                           xs -> foldl1 join xs

        oldInState = f bid
    modify (Set.delete bid)
    when ((Just bInState) /= oldInState) $ modify (Set.union (Set.fromList $ succs block))
    return $ M.insert bid bInState res

-- Terminates if fixed point for analysis found
doAnalysis :: (Eq s, LastNode l) => 
    DFAnalysis m l s -> BlockLookup m l -> M.Map BlockId s -> [Block m l] -> M.Map BlockId s
doAnalysis analysis bLookup startStates blocks =
    case Set.null workSet of
        True -> res
        False -> doAnalysis analysis bLookup res $ 
                 catMaybes $ 
                 map ((flip lookupBlock) bLookup) $
                 (Set.toList workSet)
  where fm = stepAnalysis analysis bLookup
        (res, workSet) = runState partialResult Set.empty
        partialResult = foldM fm startStates $ map getBID blocks
        getBID (Block bid _) = bid

runAnalysis :: (Eq s, LastNode l) => 
    DFAnalysis m l s -> LGraph m l -> DataflowResults m l s

runAnalysis analysis lgraph@(LGraph entryId bLookup) = 
        let blockStates = doAnalysis analysis bLookup M.empty blockList in
            DFR lgraph blockStates
   where blockList = case direction analysis of
            Forward -> postorderDFS lgraph
            Backward -> reverse $ postorderDFS lgraph

newtype AugmentedNode a s = AN { extractTuple :: (a,s) } deriving (Show, Eq, Ord)

instance (HavingSuccessors l) => HavingSuccessors (AugmentedNode l s) where
    succs (AN (l, _)) = succs l

instance (PrettyPrint a, PrettyPrint s) => PrettyPrint (AugmentedNode a s) where
    ppr (AN (x,s)) = ppr x <+> text "::    " <+> ppr s

instance (Eq s, Show s) => Show (DataflowResults m l s) where
    show (DFR _ mp) = show mp

augmentWithDFR :: (Eq s, LastNode l) => 
    DFAnalysis m l s -> LGraph m l -> LGraph (AugmentedNode m s) (AugmentedNode l s)

augmentWithDFR dfa@(DFAnalysis updateM updateL _ initState direction) lgraph@(LGraph lgentry blocks) = 
    LGraph lgentry $ mapBlocks (augmentBlock direction) blocks
  where augmentBlock Forward blk@(Block bid zt) = Block bid ztail'
           where (mids', lastState) = runState (mapM augment $ blockMiddles blk) bInState
                 bInState = blkToStates ! bid 
                 ztail' = ztailFromMiddles mids' zlast'
                 zlast' = case getZLast blk of
                     LastExit -> LastExit
                     LastOther l -> LastOther $ AN (l, lastState)

        augmentBlock Backward blk@(Block bid zt) = Block bid ztail'
           where (mids', _) = runState (mapM augment $ (reverse . blockMiddles) blk) bInState'
                 bInState = blkToStates ! bid 
                 (zlast', bInState') = case getZLast blk of
                     LastExit -> (LastExit, bInState)
                     LastOther l -> (LastOther $ AN (l, bInState), updateL l bInState)
                 ztail' = ztailFromMiddles (reverse mids') zlast'
                 
        (DFR _ blkToStates) = runAnalysis dfa lgraph
        augment m = do
            s <- get
            modify (updateM m)
            return $ AN (m, s)

foldWithDFR :: (Eq s, LastNode l) => DFAnalysis m l s -> ((Either l m, s) -> a) -> (a -> a -> a) -> a -> LGraph m l -> a
foldWithDFR dfa convert combine initVal lgraph = case dir of
        Forward -> foldl combine initVal foldedBlocks
        Backward -> foldr (flip combine) initVal foldedBlocks
    where augBlocks = postorderDFS $ augmentWithDFR dfa lgraph
          dir = direction dfa
          foldedBlocks = map (foldAugBlockWithDFR dir convert combine initVal) augBlocks

foldAugBlockWithDFR :: (Eq s, LastNode l) => 
    DFDirection -> ((Either l m, s) -> a) -> (a -> a -> a) -> a -> Block (AugmentedNode m s) (AugmentedNode l s) -> a

foldAugBlockWithDFR Forward convert combine initVal block = foldl combine initVal blockNodes
    where blockNodes = map convert $ map (mapFst Right . extractTuple) (blockMiddles block) ++ getLast (getZLast block)
          getLast (LastOther (AN (x, s))) = [(Left x, s)]
          getLast LastExit = []

foldAugBlockWithDFR Backward convert combine initVal block = foldr (flip combine) initVal blockNodes
    where blockNodes = map convert $ map (mapFst Right . extractTuple) (blockMiddles block) ++ getLast (getZLast block)
          getLast (LastOther (AN (x, s))) = [(Left x, s)]
          getLast LastExit = []

-- ============================
--- Analysis implementations
-- ============================

type AvailExprState = Set Expression

-- Available expressions analysis

availableExprAnalysis :: DFAnalysis Statement BranchingStatement AvailExprState
availableExprAnalysis = DFAnalysis {
    updateStateM = availExprUpdateM,
    updateStateL = availExprUpdateL,
    joinStates = availExprJoin,
    initState = availExprInit,
    direction = Forward
    }

availExprUpdateM :: Statement -> AvailExprState -> AvailExprState 
availExprUpdateM (Set v e) exprs = case v of
    (Var "i") -> removeKilled v $ Set.union exprs (Set.fromList $ subexpressions e)
    -- TODO: Why are these lines the same? Double check logic later.
    _         -> removeKilled v $ Set.union exprs (Set.fromList $ subexpressions e)
availExprUpdateM _ s = s

-- TODO: Fix me! This isn't the correct semantic behavior for expressions
--       in if, while, and for loop statements.  We can cache expressions
--       from these as well. 
availExprUpdateL :: BranchingStatement -> AvailExprState -> AvailExprState
availExprUpdateL _ = id

availExprJoin :: AvailExprState -> AvailExprState -> AvailExprState
availExprJoin exprs exprs' = Set.intersection exprs exprs'

availExprInit :: AvailExprState
availExprInit = Set.empty

removeKilled :: Variable -> Set Expression -> Set Expression
removeKilled var exprs = Set.filter (\e -> not (killsExpr var e)) exprs

subexpressions :: Expression -> [Expression]
subexpressions e = case e of
    expr@(Add e e') -> expr : concatMap subexpressions [e,e']
    expr@(Sub e e') -> expr : concatMap subexpressions [e,e']
    expr@(Mul e e') -> expr : concatMap subexpressions [e,e']
    expr@(Div e e') -> expr : concatMap subexpressions [e,e']
    expr@(Mod e e') -> expr : concatMap subexpressions [e,e']
    expr@(And e e') -> expr : concatMap subexpressions [e,e']
    expr@(Or e e') -> expr : concatMap subexpressions [e,e']
    expr@(Eq e e') -> expr : concatMap subexpressions [e,e']
    expr@(Lt e e') -> expr : concatMap subexpressions [e,e']
    expr@(Gt e e') -> expr : concatMap subexpressions [e,e']
    expr@(Le e e') -> expr : concatMap subexpressions [e,e']
    expr@(Ge e e') -> expr : concatMap subexpressions [e,e']
    expr@(Ne e e') -> expr : concatMap subexpressions [e,e']
    expr@(Not e) -> expr : subexpressions e
    expr@(Neg e) -> expr : subexpressions e
    _ -> []

killsExpr :: Variable -> Expression -> Bool
killsExpr var@(Scopedvar scp v) e = case e of
        Add e1 e2 -> killsExpr var e1 || killsExpr var e2
        Sub e1 e2 -> killsExpr var e1 || killsExpr var e2
        Mul e1 e2 -> killsExpr var e1 || killsExpr var e2
        Div e1 e2 -> killsExpr var e1 || killsExpr var e2
        Mod e1 e2 -> killsExpr var e1 || killsExpr var e2
        And e1 e2 -> killsExpr var e1 || killsExpr var e2
        Or e1 e2  -> killsExpr var e1 || killsExpr var e2
        Eq e1 e2  -> killsExpr var e1 || killsExpr var e2
        Lt e1 e2  -> killsExpr var e1 || killsExpr var e2
        Gt e1 e2  -> killsExpr var e1 || killsExpr var e2
        Le e1 e2  -> killsExpr var e1 || killsExpr var e2
        Ge e1 e2  -> killsExpr var e1 || killsExpr var e2
        Ne e1 e2  -> killsExpr var e1 || killsExpr var e2
        Loc (Scopedvar scp' v') -> scp == scp' && symbol v == symbol v'
        _ -> False

killsExpr var@(Var s) e = case e of
        Add e1 e2 -> killsExpr var e1 || killsExpr var e2
        Sub e1 e2 -> killsExpr var e1 || killsExpr var e2
        Mul e1 e2 -> killsExpr var e1 || killsExpr var e2
        Div e1 e2 -> killsExpr var e1 || killsExpr var e2
        Mod e1 e2 -> killsExpr var e1 || killsExpr var e2
        And e1 e2 -> killsExpr var e1 || killsExpr var e2
        Or e1 e2  -> killsExpr var e1 || killsExpr var e2
        Eq e1 e2  -> killsExpr var e1 || killsExpr var e2
        Lt e1 e2  -> killsExpr var e1 || killsExpr var e2
        Gt e1 e2  -> killsExpr var e1 || killsExpr var e2
        Le e1 e2  -> killsExpr var e1 || killsExpr var e2
        Ge e1 e2  -> killsExpr var e1 || killsExpr var e2
        Ne e1 e2  -> killsExpr var e1 || killsExpr var e2
        Loc v -> v == var
        _ -> False

killsExpr var@(Varray s _) e = case e of
        Add e1 e2 -> killsExpr var e1 || killsExpr var e2
        Sub e1 e2 -> killsExpr var e1 || killsExpr var e2
        Mul e1 e2 -> killsExpr var e1 || killsExpr var e2
        Div e1 e2 -> killsExpr var e1 || killsExpr var e2
        Mod e1 e2 -> killsExpr var e1 || killsExpr var e2
        And e1 e2 -> killsExpr var e1 || killsExpr var e2
        Or e1 e2  -> killsExpr var e1 || killsExpr var e2
        Eq e1 e2  -> killsExpr var e1 || killsExpr var e2
        Lt e1 e2  -> killsExpr var e1 || killsExpr var e2
        Gt e1 e2  -> killsExpr var e1 || killsExpr var e2
        Le e1 e2  -> killsExpr var e1 || killsExpr var e2
        Ge e1 e2  -> killsExpr var e1 || killsExpr var e2
        Ne e1 e2  -> killsExpr var e1 || killsExpr var e2
        Loc (Varray s' _) -> s == s'
        _ -> False

-- Liveness analysis for MidIR

-- Needs a better name
type LiveVarState = Set VarMarker

liveVariableAnalysis :: DFAnalysis Statement BranchingStatement LiveVarState
liveVariableAnalysis = DFAnalysis {
    updateStateM = liveVarUpdateM,
    updateStateL = liveVarUpdateL,
    joinStates = Set.union,
    initState = Set.empty,
    direction = Backward
    }

-- Needs to incorporate last nodes as well.. TODO
liveVarUpdateM :: Statement -> LiveVarState -> LiveVarState
liveVarUpdateM stmt prevState = Set.union used prevMinusDef
    where used = varsUsedInStmt stmt
          prevMinusDef = Set.difference prevState (varsDefinedInStmt stmt)

-- Needs to incorporate last nodes as well.. TODO
liveVarUpdateL :: BranchingStatement -> LiveVarState -> LiveVarState
liveVarUpdateL bStmt prevState = Set.union used prevMinusDef
    where used = varsUsedInBranchStmt bStmt
          prevMinusDef = Set.difference prevState (varsDefinedInBranchStmt bStmt)

-- Again using Data.Generics to simplify this code
varsUsedInStmt :: Statement -> Set VarMarker
varsUsedInStmt (Set (Varray _ indexExpr) expr) = 
    Set.union (everything Set.union (Set.empty `mkQ` getVariables) indexExpr)
              (everything Set.union (Set.empty `mkQ` getVariables) expr)
varsUsedInStmt (Set _ expr) = everything Set.union (Set.empty `mkQ` getVariables) expr
varsUsedInStmt (DFun _ _ _) = Set.empty
varsUsedInStmt (DVar _) = Set.empty
varsUsedInStmt stmt = everything Set.union (Set.empty `mkQ` getVariables) stmt

varsDefinedInStmt :: Statement -> Set VarMarker
varsDefinedInStmt (Set var _) = Set.singleton $ varToVarMarker var
varsDefinedInStmt (DFun _ params _) = Set.fromList $ map varToVarMarker params
varsDefinedInStmt _ = Set.empty

varsUsedInBranchStmt :: BranchingStatement -> Set VarMarker
-- TODO: See why this needs 2 expression arguments now? What changed?
varsUsedInBranchStmt (ForBranch _ expr expr' _ _) = everything Set.union (Set.empty `mkQ` getVariables) [expr, expr']
varsUsedInBranchStmt bStmt = everything Set.union (Set.empty `mkQ` getVariables) bStmt

varsDefinedInBranchStmt :: BranchingStatement -> Set VarMarker
varsDefinedInBranchStmt (ForBranch var _ _ _ _) = Set.singleton $ varToVarMarker var
varsDefinedInBranchStmt _ = Set.empty

-- Base case..
getVariables :: Variable -> Set VarMarker
getVariables v = Set.filter isScoped $ Set.singleton $ varToVarMarker v

-- Liveness analysis for LowIR

lowLVAnalysis :: DFAnalysis ProtoASM ProtoBranch LiveVarState
lowLVAnalysis = DFAnalysis {
    updateStateM = lowLVUpdateM,
    updateStateL = lowLVUpdateL,
    joinStates = Set.union,
    initState = Set.empty,
    direction = Backward
    }

lowLVUpdateM :: ProtoASM -> LiveVarState -> LiveVarState
lowLVUpdateM stmt prevState = Set.union used prevMinusDef
    where used = varsUsedInProtoStmt stmt
          prevMinusDef = Set.difference prevState (varsDefinedInProtoStmt stmt)

-- TODO: Talk with santiago and make sure this is actually the semantics of these things..
lowLVUpdateL :: ProtoBranch -> LiveVarState -> LiveVarState
lowLVUpdateL bStmt prevState = case bStmt of
        If' asms bids -> foldAsms asms
        While' asms bids -> foldAsms asms
        -- TODO: Check on how structure relates to for loop semantics
        For' v asms1 asms2 asms3 bids -> Set.unions $ map foldAsms [asms1, asms2, asms3]
        Parafor' v asms1 asms2 asms3 bids -> Set.unions $ map foldAsms [asms1, asms2, asms3]
        InitialBranch' bids -> prevState
        Jump' _ -> prevState
        Nil -> prevState
    where foldAsms = foldr lowLVUpdateM prevState

varsDefinedInProtoStmt :: ProtoASM -> Set VarMarker
varsDefinedInProtoStmt stmt = case stmt of
    Mov' _ v -> valToVMSet v
    Neg' v -> valToVMSet v
    And' _ v -> valToVMSet v
    Or' _ v -> valToVMSet v
    Add' _ v -> valToVMSet v
    Sub' _ v -> valToVMSet v -- TODO: Check semantics
    Mul' _ v -> valToVMSet v
    Div' v -> valToVMSet v -- TODO: Check semantics
    Not' v -> valToVMSet v
    Pop' v -> valToVMSet v
    CMove' _ v -> valToVMSet v
    CMovne' _ v -> valToVMSet v
    CMovg' _ v -> valToVMSet v
    CMovl' _ v -> valToVMSet v
    CMovge' _ v -> valToVMSet v
    CMovle' _ v -> valToVMSet v
    _ -> Set.empty

varsDefinedInProtoBranch :: ProtoBranch -> Set VarMarker
-- TODO: Wrong!!! For loops define variables.  FIX THIS!!
varsDefinedInProtoBranch _ = Set.empty

varsUsedInProtoStmt :: ProtoASM -> Set VarMarker
varsUsedInProtoStmt stmt = case stmt of
        Mov' v v' -> Set.union (valToVMSet v) (valsIndicesToVMSet [v,v'])
        Neg' v -> Set.union (valToVMSet v) (valIndicesToVMSet v)
        And' v v' -> Set.union (valsToVMSet [v,v']) (valsIndicesToVMSet [v,v'])
        Or'  v v' -> Set.union (valsToVMSet [v,v']) (valsIndicesToVMSet [v,v'])
        Add' v v' -> Set.union (valsToVMSet [v,v']) (valsIndicesToVMSet [v,v'])
        Sub' v v' -> Set.union (valsToVMSet [v,v']) (valsIndicesToVMSet [v,v'])
        Mul' v v' -> Set.union (valsToVMSet [v,v']) (valsIndicesToVMSet [v,v'])
        Div' v    -> Set.union (valsToVMSet [v]) (valIndicesToVMSet v)
        Lt'   v v' -> Set.union (valsToVMSet [v,v']) (valsIndicesToVMSet [v,v'])
        Gt'   v v' -> Set.union (valsToVMSet [v,v']) (valsIndicesToVMSet [v,v'])
        Le'   v v' -> Set.union (valsToVMSet [v,v']) (valsIndicesToVMSet [v,v'])
        Ge'   v v' -> Set.union (valsToVMSet [v,v']) (valsIndicesToVMSet [v,v'])
        Eq'   v v' -> Set.union (valsToVMSet [v,v']) (valsIndicesToVMSet [v,v'])
        Ne'   v v' -> Set.union (valsToVMSet [v,v']) (valsIndicesToVMSet [v,v'])
        Not'  v  -> Set.union (valToVMSet v) (valIndicesToVMSet v)
        Cmp' v v' -> Set.union (valsToVMSet [v,v']) (valsIndicesToVMSet [v,v'])
        CMove' v v' -> Set.union (valToVMSet v) (valsIndicesToVMSet [v,v'])
        CMovne' v v' -> Set.union (valToVMSet v) (valsIndicesToVMSet [v,v'])
        CMovg' v v' -> Set.union (valToVMSet v) (valsIndicesToVMSet [v,v'])
        CMovl' v v' -> Set.union (valToVMSet v) (valsIndicesToVMSet [v,v'])
        CMovge' v v' -> Set.union (valToVMSet v) (valsIndicesToVMSet [v,v'])
        CMovle' v v' -> Set.union (valToVMSet v) (valsIndicesToVMSet [v,v'])
        _ -> Set.empty

varsUsedInProtoBranch :: ProtoBranch -> Set VarMarker
-- TODO: SO WRONG!! FIX ME!!
varsUsedInProtoBranch bStmt = Set.empty

