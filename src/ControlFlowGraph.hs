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
stmtToAGraph (DFun name params body) = 
    mkMethod name $ stmtsToAGraph body

stmtToAGraph x = mkMiddle x

-- Pretty Printing

instance PrettyPrint Expression where
    ppr (Add e1 e2) = parens $ (ppr e1) <+> text "+" <+> (ppr e2)
    ppr (Sub e1 e2) = parens $ (ppr e1) <+> text "-" <+> (ppr e2)
    ppr (Mul e1 e2) = parens $ (ppr e1) <+> text "*" <+> (ppr e2)
    ppr (Div e1 e2) = parens $ (ppr e1) <+> text "/" <+> (ppr e2)
    ppr (Mod e1 e2) = parens $ (ppr e1) <+> text "%" <+> (ppr e2)
    ppr (And e1 e2) = parens $ (ppr e1) <+> text "&&" <+> (ppr e2)
    ppr (Or e1 e2) = parens $ (ppr e1) <+> text "||" <+> (ppr e2)
    ppr (Eq e1 e2) = parens $ (ppr e1) <+> text "==" <+> (ppr e2)
    ppr (Lt e1 e2) = parens $ (ppr e1) <+> text "<" <+> (ppr e2)
    ppr (Gt e1 e2) = parens $ (ppr e1) <+> text ">" <+> (ppr e2)
    ppr (Le e1 e2) = parens $ (ppr e1) <+> text "<=" <+> (ppr e2)
    ppr (Ge e1 e2) = parens $ (ppr e1) <+> text ">=" <+> (ppr e2)
    ppr (Ne e1 e2) = parens $ (ppr e1) <+> text "!=" <+> (ppr e2)
    ppr (Not e) = text "!" <+> parens (ppr e)
    ppr (Neg e) = text "-" <+> parens (ppr e)
    ppr (Const i) = int i
    ppr (Str s) = doubleQuotes $ text s
    ppr (Loc v) = ppr v
    ppr (FuncCall name ps) = text name <+> prettyParams
        where prettyParams = foldl f lparen ps <+> rparen
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
        where prettyParams = foldl f lparen ps <+> rparen
              f acc p = acc <+> ppr p <> comma
    ppr (Callout name ps) = text name <+> prettyParams
        where prettyParams = foldl f lparen ps <+> rparen
              f acc p = acc <+> ppr p <> comma

instance PrettyPrint BranchingStatement where
    ppr (Jump bid) = text "Jump" <+> ppr bid
    ppr (IfBranch e bid1 bid2) = text "If" <+> parens (ppr e) <+>
                                 text "then:" <+> ppr bid1 <+>
                                 text "else:" <+> ppr bid2
    ppr (WhileBranch e bid1 bid2) = text "While" <+> parens (ppr e) <+>
                                 text "loop:" <+> ppr bid1 <+>
                                 text "end:" <+> ppr bid2
