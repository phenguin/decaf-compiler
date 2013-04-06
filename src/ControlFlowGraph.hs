module ControlFlowGraph where

import CFGConcrete
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

stmtToAGraph x = mkMiddle x

-- Pretty Printing

instance PrettyPrint Expression where
    ppr (Sub e1 e2) = parens (ppr e1) <+> text "-" <+> parens (ppr e1)
    ppr (Mul e1 e2) = parens (ppr e1) <+> text "*" <+> parens (ppr e1)
    ppr (Div e1 e2) = parens (ppr e1) <+> text "/" <+> parens (ppr e1)
    ppr (Mod e1 e2) = parens (ppr e1) <+> text "%" <+> parens (ppr e1)
    ppr (And e1 e2) = parens (ppr e1) <+> text "&&" <+> parens (ppr e1)
    ppr (Or e1 e2) = parens (ppr e1) <+> text "||" <+> parens (ppr e1)
    ppr (Eq e1 e2) = parens (ppr e1) <+> text "==" <+> parens (ppr e1)
    ppr (Lt e1 e2) = parens (ppr e1) <+> text "<" <+> parens (ppr e1)
    ppr (Gt e1 e2) = parens (ppr e1) <+> text ">" <+> parens (ppr e1)
    ppr (Le e1 e2) = parens (ppr e1) <+> text "<=" <+> parens (ppr e1)
    ppr (Ge e1 e2) = parens (ppr e1) <+> text ">=" <+> parens (ppr e1)
    ppr (Ne e1 e2) = parens (ppr e1) <+> text "!=" <+> parens (ppr e1)
    ppr (Not e) = text "!" <+> parens (ppr e)
    ppr (Neg e) = text "-" <+> parens (ppr e)
    ppr (Const i) = int i
    ppr (Str s) = text s
    ppr (Loc v) = ppr v
    ppr (FuncCall name ps) = text name <+> prettyParams
        where prettyParams = foldl f lparen ps
              f acc p = acc <+> ppr p <> comma

instance PrettyPrint Variable where
    ppr (Var name) = text name
    ppr (Varray name e) = text name <> lbrack <+>
                          ppr e <+> rbrack

instance PrettyPrint Statement where
    ppr (If _ _ _) = text "If Statement which shouldnt be here"
    ppr (While _ _) = text "While Statement which shouldn't be here"
    ppr (Return e) = text "return" <+> ppr e
    ppr Break = text "break"
    ppr Continue = text "continue"
    ppr (Set v e) = ppr v <+> text "=" <+> ppr e
    ppr (DVar v e) = ppr v <+> text "=" <+> ppr e
    ppr (Function name ps) = text name <+> prettyParams
        where prettyParams = foldl f lparen ps
              f acc p = acc <+> ppr p <> comma
    ppr (Callout name ps) = text name <+> prettyParams
        where prettyParams = foldl f lparen ps
              f acc p = acc <+> ppr p <> comma

instance PrettyPrint BranchingStatement where
    ppr (Jump bid) = text "Jump" <+> ppr bid
    ppr (IfBranch e bid1 bid2) = text "If" <+> parens (ppr e) <+>
                                 text "then:" <+> ppr bid1 <+>
                                 text "else:" <+> ppr bid2
    ppr (WhileBranch e bid1 bid2) = text "While" <+> parens (ppr e) <+>
                                 text "loop:" <+> ppr bid1 <+>
                                 text "end:" <+> ppr bid2
