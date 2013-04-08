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
import Optimization 
import qualified Data.Set as Set
import qualified Data.Map as M
import Text.PrettyPrint.HughesPJ

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

data DFAnalysis m l s = DFAnalysis {
    -- Computes output state of block from input state
    -- maybe need to add update state for last node?
    update_state :: m -> s -> s,
    -- Combines states
    join_func :: s -> s -> s,
    initState :: s
    }

computeTransferFunc :: (PrettyPrint l, LastNode l, PrettyPrint m) =>
    DFAnalysis m l s -> Block m l -> s -> s
computeTransferFunc (DFAnalysis update_func _ _) block inState = foldl (flip update_func) inState $ blockMiddles block

stepAnalysis :: (Eq s, PrettyPrint m, PrettyPrint l, LastNode l, PrettyPrint s) => 
    DFAnalysis m l s -> BlockLookup m l -> M.Map BlockId s -> BlockId -> State (Set BlockId) (M.Map BlockId s)

stepAnalysis dfa@(DFAnalysis updateF join initState) bLookup res bid = do
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

        debugStr = "Computed for " ++ pPrint bid ++ ": " ++ pPrint bInState ++ " from Preds:\n" ++ pPrint predsWithOutStates
        oldInState = trace debugStr $ f bid
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
    let blockStates = doAnalysis analysis bLookup M.empty (postorderDFS lgraph) in
        DFR lgraph blockStates
        
--- Analysis implementations

type GenSet = M.Map Expression Int
type KillSet = Set Variable
type AvailExprState = Set Expression

-- Available expressions analysis

availableExprAnalysis :: (PrettyPrint l, LastNode l) => DFAnalysis Statement l AvailExprState
availableExprAnalysis = DFAnalysis availExprUpdateState availExprJoin availExprInit

availExprUpdateState :: Statement -> AvailExprState -> AvailExprState 
availExprUpdateState (Set v e) exprs = case v of
    (Var "i") -> let debugStr = "availExprUpdateState for set i stmt:\n" ++ "v: " ++ pPrint v ++ "\nExprs: " ++ pPrint exprs ++ "\nafter: " ++ pPrint (removeKilled v exprs) in
                     trace debugStr $ removeKilled v $ Set.union exprs (Set.fromList $ subexpressions e)
    _ -> removeKilled v $ Set.union exprs (Set.fromList $ subexpressions e)
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

