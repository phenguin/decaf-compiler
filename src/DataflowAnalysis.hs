module DataflowAnalysis where

import CFGConcrete
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
import Text.PrettyPrint.HughesPJ
import Data.Generics

data DataflowResults m l s = DFR (LGraph m l) (M.Map BlockId s) deriving (Eq)

instance (Eq s, Show s) => Show (DataflowResults m l s) where
    show (DFR _ mp) = show mp

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
    update_state :: m -> s -> s,
    -- Combines states
    join_func :: s -> s -> s,
    initState :: s,
    direction :: DFDirection
    }

computeTransferFunc :: (PrettyPrint l, LastNode l, PrettyPrint m) =>
    DFAnalysis m l s -> Block m l -> s -> s
computeTransferFunc (DFAnalysis update_func _ _ Forward) block inState = foldl (flip update_func) inState $ blockMiddles block
computeTransferFunc (DFAnalysis update_func _ _ Backward) block inState = foldl (flip update_func) inState $ reverse (blockMiddles block)

stepAnalysis :: (Eq s, PrettyPrint m, PrettyPrint l, LastNode l, PrettyPrint s) => 
    DFAnalysis m l s -> BlockLookup m l -> M.Map BlockId s -> BlockId -> State (Set BlockId) (M.Map BlockId s)

stepAnalysis dfa@(DFAnalysis updateF join initState Forward) bLookup res bid = do
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

stepAnalysis dfa@(DFAnalysis updateF join initState Backward) bLookup res bid = do
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
doAnalysis :: (PrettyPrint s, Eq s, PrettyPrint l, PrettyPrint m, LastNode l) => 
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

runAnalysis :: (Eq s, PrettyPrint s, PrettyPrint l, PrettyPrint m, LastNode l) => 
    DFAnalysis m l s -> LGraph m l -> DataflowResults m l s

runAnalysis analysis lgraph@(LGraph entryId bLookup) = 
        let blockStates = doAnalysis analysis bLookup M.empty blockList in
            DFR lgraph blockStates
   where blockList = case direction analysis of
            Forward -> postorderDFS lgraph
            Backward -> reverse $ postorderDFS lgraph
        
-- ============================
--- Analysis implementations
-- ============================

type AvailExprState = Set Expression

-- Available expressions analysis

availableExprAnalysis :: (PrettyPrint l, LastNode l) => DFAnalysis Statement l AvailExprState
availableExprAnalysis = DFAnalysis availExprUpdateState availExprJoin availExprInit Forward

availExprUpdateState :: Statement -> AvailExprState -> AvailExprState 
availExprUpdateState (Set v e) exprs = case v of
    (Var "i") -> removeKilled v $ Set.union exprs (Set.fromList $ subexpressions e)
    _         -> removeKilled v $ Set.union exprs (Set.fromList $ subexpressions e)
availExprUpdateState _ s = s

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

-- Liveness analysis

type LiveVarState = Set Variable

liveVariableAnalysis :: (PrettyPrint l, LastNode l) => 
    DFAnalysis Statement l LiveVarState
liveVariableAnalysis = DFAnalysis liveVarUpdateState liveVarJoin liveVarInit Backward

-- Needs to incorporate last nodes as well.. TODO
liveVarUpdateState :: Statement -> LiveVarState -> LiveVarState
liveVarUpdateState stmt prevState = Set.union used prevMinusDef
    where used = usedVars stmt
          prevMinusDef = Set.difference prevState (definedVars stmt)

liveVarJoin :: LiveVarState -> LiveVarState -> LiveVarState
liveVarJoin = Set.union

liveVarInit :: LiveVarState
liveVarInit = Set.empty

-- Again using Data.Generics to simplify this code
usedVars :: Statement -> Set Variable
usedVars (Set _ expr) = everything Set.union (Set.empty `mkQ` getVariables) expr
usedVars stmt = everything Set.union (Set.empty `mkQ` getVariables) stmt

definedVars :: Statement -> Set Variable
definedVars (Set var _) = Set.singleton var
definedVars _ = Set.empty

-- Base case..
getVariables :: Variable -> Set Variable
getVariables var = Set.singleton var
