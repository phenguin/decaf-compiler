module DataflowAnalysis where

import CFGConcrete
import Debug.Trace (trace)
import Data.List (foldl1)
import Control.Applicative
import PrettyPrint
import CFGConstruct
import Control.Monad
import Control.Monad.State
import Data.Maybe (isJust, fromJust)
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
    transfer_func :: Block m l -> s -> s,
    -- Combines states
    join_func :: s -> s -> s,
    initState :: s
    }

stepAnalysis :: (Eq s, PrettyPrint m, PrettyPrint l, LastNode l, PrettyPrint s) => 
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
        bInState = foldl join initState $  map (uncurry trans) predsWithStates
    modify (Set.delete bid)
    when (bInState /= oldInState) $ modify (Set.union (Set.fromList $ succs block))
    return $ M.insert bid bInState res

-- Terminates if fixed point for analysis found
doAnalysis :: (PrettyPrint s, Eq s, PrettyPrint l, PrettyPrint m, LastNode l) => 
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

runAnalysis :: (Eq s, PrettyPrint s, PrettyPrint l, PrettyPrint m, LastNode l) => 
    DFAnalysis m l s -> LGraph m l -> DataflowResults m l s

runAnalysis analysis lgraph@(LGraph entryId bLookup) =
    let blockStates = doAnalysis analysis bLookup M.empty (postorderDFS lgraph) in
        DFR lgraph blockStates
        
--- Test analysis
--
-- SHitty test analysis
countUpTo :: (PrettyPrint m, PrettyPrint l, LastNode l) => Int -> DFAnalysis m l Int
countUpTo n = DFAnalysis trans join 0
    where trans (Block (BID str) (ZLast _)) s = min (s + 1) n
          trans (Block bid (ZTail _ zt)) s = trans (Block bid zt) $ min (s+1) n
          join s1 s2 = min n $ max s1 s2

type GenSet = M.Map Expression Int
type KillSet = Set Variable
newtype AvailExprState = AES { extractAES :: (GenSet, KillSet) } deriving (Eq, Ord, Show)

instance PrettyPrint AvailExprState where
    ppr (AES (gen, kill)) = trace ("gen:" ++ pPrint gen) $ text "Gen:" <+> (hsep $ map ppr (M.keys gen)) $$
                            text "Kill:" <+> (hsep $ map ppr (Set.toList kill))

-- Available expressions analysis

availableExprAnalysis :: (PrettyPrint l, LastNode l) => DFAnalysis Statement l AvailExprState
availableExprAnalysis = DFAnalysis availExprTrans availExprJoin availExprInit

stepTrans :: Statement -> AvailExprState -> AvailExprState 
stepTrans (Set v e) (AES (gen, kill)) = AES (gen', kill')
    -- temporary for gen
    where gen' = M.union gen (M.fromList $ zip (subexpressions e) [0..])
          kill' = Set.insert v kill
stepTrans _ s = s

availExprTrans :: (PrettyPrint l, LastNode l) =>
    Block Statement l -> AvailExprState -> AvailExprState
availExprTrans block inState = foldl (flip stepTrans) inState $ blockMiddles block

availExprJoin :: AvailExprState -> AvailExprState -> AvailExprState
availExprJoin (AES (gen, kill)) (AES (gen', kill')) = AES (gen'', kill'')
    where gen'' = M.intersection gen gen'
          kill'' = Set.union kill kill'

availExprInit :: AvailExprState
availExprInit = AES (M.empty, Set.empty)

removeKilled :: Variable -> GenSet -> GenSet
removeKilled var gen = M.filterWithKey (\e _ -> not (killsExpr var e)) gen

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

