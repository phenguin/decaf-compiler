module ControlFlowGraph where

import CFGConcrete
import Debug.Trace
import Text.PrettyPrint.HughesPJ hiding (Str)
import PrettyPrint
import CFGConstruct
import Optimization

type ControlFlowGraph = AGraph Statement BranchingStatement

data BranchingStatement = Jump BlockId | IfBranch Expression BlockId BlockId | WhileBranch Expression BlockId BlockId -- | Continue | Break ... Not yet done

instance HavingSuccessors BranchingStatement where
    succs (Jump bid) = [bid]
    succs (IfBranch _ bid1 bid2) = [bid1, bid2]
    succs (WhileBranch _ bid1 bid2) = [bid1, bid2]

instance LastNode BranchingStatement where
    mkBranchNode bid = Jump bid
    isBranchNode s = case s of
        Jump _ -> True
        _ -> False

makeCFG :: Program -> ControlFlowGraph
makeCFG (Prg stmts) = stmtsToAGraph stmts

stmtsToAGraph :: [Statement] -> ControlFlowGraph
stmtsToAGraph stmts = foldAGraphs $ map stmtToAGraph stmts

stmtToAGraph :: Statement -> ControlFlowGraph
stmtToAGraph (If cond thendo elsedo) = 
            mkIfElse cbranch (stmtsToAGraph thendo) (stmtsToAGraph elsedo)
    where cbranch bid1 bid2 = mkLast $ IfBranch cond bid1 bid2

stmtToAGraph (While cond body) = 
            mkWhile cbranch (stmtsToAGraph body)
    where cbranch bid1 bid2 = mkLast $ WhileBranch cond bid1 bid2

-- Ignore parameters for now.. perhaps this should be a statement..
stmtToAGraph st@(DFun name params body) = 
    mkMethod name (mkMiddle st) $ stmtsToAGraph body

stmtToAGraph x = mkMiddle x

-- -- Skeleton code for santiago --- asm conversion
-- ===================================================
-- type LowCFG :: LGraph ProtoASM [ProtoASM]
-- toLowIRCFG :: ControlFlowGraph -> LowCFG
-- toLowIRCFG cfg = mapLGraphNodes mapStmtToAsm mapBranchToAsm cfgLGraph
--     where cfgLGraph = lgraphFromAGraphBlocks (BID "main")

-- -- Converts regular statements to the pseudo-asm code
-- mapStmtToAsm :: Statement -> [ProtoASM]
-- mapStmtToAsm = undefined

-- -- Need newtype because the type needs to be made instance of LastNode
-- newtype BranchSeq = BranchSeq [ProtoASM] deriving (Eq, Ord)

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
