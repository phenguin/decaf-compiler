module LowIR where 

import Optimization
import qualified Data.Map 
import ControlFlowGraph
import CFGConstruct
import CFGConcrete
import PrettyPrint
import Text.PrettyPrint.HughesPJ hiding (Str)
import Debug.Trace

data Value = Symbol String | Array String Value | Literal Int | EvilString String | L | R 
		deriving (Show,Eq,Ord)
	
data ProtoASM = Dec' Value
	| Mov' Value Value
	| Neg' Value 
	| And' Value Value
	| Or'  Value Value
	| Add' Value Value
	| Sub' Value Value
	| Mul' Value Value
	| Div' Value Value
	| Lt'   Value Value
	| Gt'   Value Value
	| Le'   Value Value
	| Ge'   Value Value
	| Eq'   Value Value
	| Ne'   Value Value
	| Not'  Value 
	| Ret'  Value
	| Callout' [Value]
	| Str' Value
	| Cmp' Value Value
	| Je' BlockId
	| Jmp' BlockId
	deriving (Show,Eq,Ord)

data ProtoBranch =  Jump' [ProtoASM] BlockId
	| If' [ProtoASM] [BlockId]
	| While' [ProtoASM] [BlockId]
	deriving (Show,Eq,Ord)

newtype ProtoASMList = ProtoASMList [ProtoASM]

instance PrettyPrint ProtoASMList where
    ppr (ProtoASMList bs) = text "<End Block>" $$ text "Branch Targets:" <+> (hsep $ map ppr bs) $$ text ""


instance HavingSuccessors ProtoBranch where
	succs x = case x of
		(Jump' _ b1) 	-> [b1]
		(If' _ x) 	-> x
		(While' _ x)    -> x

instance LastNode ProtoBranch where
	mkBranchNode bid = Jump' [Jmp' bid]  bid
	isBranchNode s = case s of
		Jump' _ _ 	-> True
		If' _ _ -> True
		While' _ _ -> True
		_ 	-> False


--newtype CSEnv = Data.Map.Map  Expression Expression

--cse:: ControlFlowGraph -> Either a [IO()]


type LowCFG = LGraph ProtoASM ProtoBranch

toLowIRCFG :: ControlFlowGraph -> LowCFG
toLowIRCFG cfg = mapLGraphNodes (mapStmtToAsm) (mapBranchToAsm) cfgLGraph
      where cfgLGraph = lgraphFromAGraphBlocks (BID "main") cfg

-- Converts regular statements to the pseudo-asm code
mapStmtToAsm :: BlockId -> Statement -> [ProtoASM]
mapStmtToAsm bid x = case x of
        (Set var expr) -> (mapExprToAsm expr) ++ [Mov' L (mapVarToValue var)]
        (DVar var)-> [Dec' (mapVarToValue var)]
	_ 	-> Debug.Trace.trace (show x) []

mapVarToValue (Var str) = Symbol str
mapVarToValue (Varray str (Const i)) =  Array str (Literal i)

mapExprToAsm::Expression -> [ProtoASM]
mapExprToAsm x = case x of
                (Sub x y)       -> binop (Sub') x y
                (Add x y)       -> binop (Add') x y
                (Mul x y)       -> binop (Mul') x y
                (Div x y)       -> binop (Div') x y
                (And x y)       -> binop (And') x y
                (Or x y)        -> binop (Or') x y
                (Lt x y)        -> binop (Lt') x y
                (Gt x y)        -> binop (Gt') x y
                (Le x y)        -> binop (Le') x y
                (Ge x y)        -> binop (Ge') x y
                (Ne x y)        -> binop (Ne') x y
                (Eq x y)        -> binop (Eq') x y
                (Not x )        -> uniop (Not') x
                (Neg x)         -> uniop (Neg') x
                (Const i)       -> [Mov' (Literal i) L]
                (Loc (Var x))   -> [Mov' (Symbol x) L]
                (Loc (Varray x i))-> let pi = process i in 
					pi ++ [(Mov' R L),(Mov' (Array x R) L)]
                (Str str)       -> [Mov' (EvilString str) L]
		_ 	-> Debug.Trace.trace (show x) []
                where
                        binop t x y = let px = process x
                                          py = process y in
                                        (px
                                         ++[Mov' L R]
                                         ++ py
                                         ++ [t R L])
                        uniop t x  = let px = process x in
                                        (px
                                         ++ [t L])
                        process = mapExprToAsm

-- -- Skeleton code for santiago --- asm conversion
-- ===================================================

-- Converts regular statements to the pseudo-asm code
-- -- Need newtype because the type needs to be made instance of LastNode

-- -- converts branching statements to a branch seq of asm ops and
-- -- possibly some additional preamble.  probably will want to return
-- -- ([], BranchSeq <stuff>)
mapBranchToAsm :: BlockId-> ZLast BranchingStatement -> ([ProtoASM], ZLast ProtoBranch)
mapBranchToAsm bid (LastOther (IfBranch expr bid1 bid2))  
	= ([], LastOther $ If' (expressed++[(Cmp' L (Literal 0)),(Je' bid2)]) [bid1, bid2])
	where expressed = mapExprToAsm expr
mapBranchToAsm bid (LastOther (Jump bid1))  = ([], LastOther $ Jump' [Jmp' bid1] bid1)
mapBranchToAsm bid (LastOther (WhileBranch expr bid1 bid2))  
	= ([], LastOther $ While' (expressed++[(Cmp' L (Literal 0)),(Je' bid2)]) [bid1, bid2])
	where expressed = mapExprToAsm expr
mapBranchToAsm bid (LastExit) = ([],LastExit)
-- Pretty Printing
instance PrettyPrint ProtoASM where
	ppr asm = case asm of 
                (Sub' x y)       -> binop "SUB" x y
                (Add' x y)       -> binop "ADD" x y
                (Mul' x y)       -> binop "MUL" x y
                (Div' x y)       -> binop "DIV" x y
                (And' x y)       -> binop "AND" x y
                (Or' x y)        -> binop "OR" x y
                (Lt' x y)        -> binop "LT" x y
                (Gt' x y)        -> binop "GT" x y
                (Le' x y)        -> binop "LE" x y
                (Ge' x y)        -> binop "GE" x y
                (Ne' x y)        -> binop "NE" x y
                (Eq' x y)        -> binop "EQ" x y
                (Not' x )        -> uniop "NOT" x
                (Neg' x)         -> uniop "NEG" x
                (Mov' x y)	 -> binop "MOV" x y
		_ 		 -> Debug.Trace.trace (show asm) (text "@@")
	  where 
  	    binop name x y = text (name++" ") <+> (ppr x) <+> text"," <+> (ppr y) 
	    uniop name x  = text (name++" " )<+> (ppr x)  

instance PrettyPrint Value where
	ppr x = case x of 
		(Symbol str) 		-> text str 
		(Array str i) 		-> text (str ++ "[") <+> ppr i <+> text "]"
		(Literal i)		-> text $ show i
		(EvilString str) 	-> text $ show str
		(L) 			-> text "L"
		(R)			-> text "R"


instance PrettyPrint ProtoBranch where
    ppr (Jump' _ bid) = text "Jump" <+> ppr bid
    ppr (If' e [bid1, bid2]) = text "If" <+> parens (hsep $ map ppr  e) <+>
                                 text "then:" <+> ppr bid1 <+>
                                 text "else:" <+> ppr bid2
    ppr (While' e [bid1,bid2]) = text "While" <+> parens (hsep$ map ppr e) <+>
                                 text "loop:" <+> ppr bid1 <+>
				 text "end:" <+> ppr bid2 

{--toLowIR = lowIRProg


lowIRPrg a statements = Prg' (lowIRGlobals DVars):(map lowIRFun DFuns)
	where
	  DVars = filter isDVar statements
	  isDVar (DVar _ _) = True
	  isDVar _ = False
	  DFuns = filter isDFun statements
	  isDFun (DFun _ _ _) = True
	  isDFun _ = False 

lowIRGlobals (DVar (Variable) Expression):dvars =  () 
--}
