{-# LANGUAGE DeriveDataTypeable #-}
module ControlFlowGraph where


import CFGConcrete
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (sort, groupBy, isPrefixOf)
import qualified Data.Map as M
import Debug.Trace
import Text.PrettyPrint.HughesPJ hiding (Str)
import PrettyPrint
import CFGConstruct
import MidIR
import MonadUniqueEnv
import Data.Generics

type ControlFlowGraph = AGraph Statement BranchingStatement

lgraphSpanningFunctions :: ControlFlowGraph -> LGraph Statement BranchingStatement
lgraphSpanningFunctions agraph@(AGraph g) = removeUniqEnv $ do
    bid <- newBlockId "Start"
    Graph _ oldBlks <- g emptyGraph
    let allFuncBids = map BID $ filter (not . ("." `isPrefixOf`)) $ map (getStr . bId) $ M.elems oldBlks
        AGraph f = mkLabel bid <&> mkLast (InitialBranch allFuncBids) <&> agraph
    Graph _ blocks <- f emptyGraph
    return $ LGraph bid blocks

data BranchingStatement = Jump BlockId 
                        | IfBranch Expression BlockId BlockId 
                        | WhileBranch Expression BlockId BlockId
                        | ForBranch Variable Expression Expression BlockId BlockId
                        | ParaforBranch Variable Expression Expression BlockId BlockId
                        -- Initialbranch used to ensure all functions are included in the DFS
                        | InitialBranch [BlockId]-- | Continue | Break ... Not yet done
                        | None
			deriving (Show, Eq, Data, Typeable)

instance HavingSuccessors BranchingStatement where
    succs (Jump bid) = [bid]
    succs (IfBranch _ bid1 bid2) = [bid1, bid2]
    succs (WhileBranch _ bid1 bid2) = [bid1, bid2]
    succs (ForBranch _ _ _ bid1 bid2) = [bid1, bid2]
    succs (ParaforBranch _ _ _ bid1 bid2) = [bid1, bid2]
    succs (InitialBranch bs) = bs

instance LastNode BranchingStatement where
    mkBranchNode bid = Jump bid
    isBranchNode s = case s of
        Jump _ -> True
        _ -> False

allNonArrayVarsForMidCfg :: (LastNode l, Data l) => LGraph Statement l -> Set String
allNonArrayVarsForMidCfg = everything Set.union (Set.empty `mkQ` selectVariable)

selectVariable :: Variable -> Set String
selectVariable var = case isArray var of
    True -> Set.empty
    False -> Set.singleton $ symbol var
  where isArray (Varray _ _) = True
        isArray _ = False

getFunctionParamMap :: LGraph Statement BranchingStatement -> M.Map String [Variable]
getFunctionParamMap (LGraph _ bLookup) = 
                              M.fromList $ map mapF $
                              filter filterF $ 
                              concatMap blockMiddles (M.elems bLookup)
    where filterF (DFun _ _ _) = True
          filterF _ = False
          mapF (DFun s params _) = (s, params)

makeCFG :: Program -> ControlFlowGraph
makeCFG (Prg stmts) = stmtsToAGraph stmts

stmtsToAGraph :: [Statement] -> ControlFlowGraph
stmtsToAGraph stmts = foldAGraphs $ map stmtToAGraph stmts

stmtToAGraph :: Statement -> ControlFlowGraph
stmtToAGraph (If cond thendo elsedo) = 
            mkIfElse cbranch (stmtsToAGraph thendo) (stmtsToAGraph elsedo)
    where cbranch bid1 bid2 = mkLast $ IfBranch cond bid1 bid2

stmtToAGraph (ForLoop var start cond body) = 
            mkFor cbranch (stmtsToAGraph body)
    where cbranch bid1 bid2 = mkLast $ ForBranch var start cond bid1 bid2

stmtToAGraph (Parafor var start cond body) = 
            mkParafor cbranch (stmtsToAGraph body)
    where cbranch bid1 bid2 = mkLast $ ParaforBranch var start cond bid1 bid2

stmtToAGraph (While cond body) = 
            mkWhile cbranch (stmtsToAGraph body)
    where cbranch bid1 bid2 = mkLast $ WhileBranch cond bid1 bid2

-- Ignore parameters for now.. perhaps this should be a statement..
stmtToAGraph st@(DFun name params body) = 
    mkMethod name (mkMiddle st) $ stmtsToAGraph body

stmtToAGraph x = mkMiddle x

-- -- Skeleton code for santiago --- asm conversion
-- ===================================================

-- Converts regular statements to the pseudo-asm code
-- -- Need newtype because the type needs to be made instance of LastNode
-- newtype BranchSeq = BranchSeq [ProtoASM] [BlockId] deriving (Eq, Ord)

-- -- converts branching statements to a branch seq of asm ops and 
-- -- possibly some additional preamble.  probably will want to return
-- -- ([], BranchSeq <stuff>)
-- mapBranchToAsm :: BranchingStatement -> ([ProtoASM], BranchSeq)
-- mapBranchToAsm = undefined

-- instance HavingSuccessors BranchingStatement where
--     succs (BranchSeq istrs) = length $ filter f istrs
--         where f (Jump _) = True
--               f _ = False

-- instance LastNode BranchingStatement where
--     mkBranchNode bid = BranchSeq [Jump bid]

-- Pretty Printing

instance PrettyPrint BranchingStatement where
    ppr (Jump bid) = text "Jump" <+> ppr bid
    ppr (IfBranch e bid1 bid2) = text "If" <+> parens (ppr e) <+>
                                 text "then:" <+> ppr bid1 <+>
                                 text "else:" <+> ppr bid2
    ppr (WhileBranch e bid1 bid2) = text "While" <+> parens (ppr e) <+>
                                 text "loop:" <+> ppr bid1 <+>
                                 text "end:" <+> ppr bid2
    ppr (ForBranch v s e bid1 bid2) = text "For " <+> parens (ppr s <+> text "->"<+>ppr e) <+>
                                 text "loop:" <+> ppr bid1 <+>
                                 text "end:" <+> ppr bid2
    ppr (ParaforBranch v s e bid1 bid2) = text "Parafor " <+> parens (ppr s <+> text "->"<+>ppr e) <+>
                                 text "loop:" <+> ppr bid1 <+>
                                 text "end:" <+> ppr bid2
    ppr (InitialBranch bids) = text "Declared Functions:" <+> hsep (map ppr bids)
