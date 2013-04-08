module LowIR where 

import Optimization
import qualified Data.Map 
import ControlFlowGraph
import CFGConstruct
import CFGConcrete
import PrettyPrint
import Text.PrettyPrint.HughesPJ hiding (Str)
import Debug.Trace

data Value = Symbol String | Array String Value | Literal Int | EvilString{getString::String} | Label String
		| RAX | RBX | RCX | RDX | RSP | RBP | RSI | RDI | R8 | R9 | R10 | R11 
		| R12 | R13 | R14 | R15 
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
	| Call' String 
	| Str' Value
	| Cmp' Value Value
	| Je' BlockId
	| Jmp' BlockId
	| Pop' Value
	| Push' Value
	deriving (Show,Eq,Ord)
saveFrame = [RBX, RSP, RBP, R12,R13,R14,R15] 
save::[ProtoASM]
save	= map Push' saveFrame
restore::[ProtoASM]
restore = map Pop' (reverse saveFrame)

data ProtoBranch =  Jump' [ProtoASM] BlockId
	| If' [ProtoASM] [BlockId]
	| While' [ProtoASM] [BlockId]
	deriving (Show,Eq,Ord)

newtype ProtoASMR12ist = ProtoASMR12ist [ProtoASM]

instance PrettyPrint ProtoASMR12ist where
    ppr (ProtoASMR12ist bs) = text "<End Block>" $$ text "Branch Targets:" <+> (hsep $ map ppr bs) $$ text ""


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
        (Set var expr) -> (mapExprToAsm expr) ++ [Mov' R12 R14] ++ (mapVarToValue var) ++
			[Mov' R14 R12]
        (DVar (Var str))-> [Dec' (Symbol str)]
        (DVar (Varray str (Const i)))-> [Dec' (Array str (Literal i))]
        (Callout str param)-> protoMethodCall (FuncCall str param)
	(Function name param) -> protoMethodCall (FuncCall name param)
	_ 	-> Debug.Trace.trace ("!!STMT!" ++ (show x)) []


	
mapVarToValue (Var str) = [Mov' R12 (Symbol str)]
mapVarToValue (Varray str expr) =   (mapExprToAsm expr) ++ [Mov' R12 (Array str R12)]
mapVarToValue x = Debug.Trace.trace ("!!VAR!" ++ (show x)) [Mov' (Symbol "OHFUCK") (Symbol "ERROR")]

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
                (Const i)       -> [Mov' (Literal i) R12]
                (Loc (Var x))   -> [Mov' (Symbol x) R12]
                (Loc (Varray x i))-> let pi = process i in 
					pi ++ [(Mov' R13 R12),(Mov' (Array x R13) R12)]
                (Str str)       -> [Mov' (EvilString str) R12]
		(FuncCall n p )	-> protoMethodCall x 
		_ 	-> Debug.Trace.trace ( "!EXPR!!" ++ (show x)) []
                where
                        binop t x y = let px = process x
                                          py = process y in
                                        (px
                                         ++[Mov' R12 R13]
                                         ++ py
                                         ++ [t R13 R12])
                        uniop t x  = let px = process x in
                                        (px
                                         ++ [t R12])
                        process = mapExprToAsm

protoMethodCall:: Expression -> [ProtoASM]
protoMethodCall (FuncCall name midParam) =
    	save
        ++ params
        ++ (if name == "printf" then [Mov' (Literal 0) RAX] else [])
        ++ [Call' name]
        ++ [(Pop' RBX) | x<- [1..((length params) - 6)]]
    	++ restore
                where   params =  makeparam midParam 0
                        makeparam ((Str str):xs) i =
                                flipAfter5 i [param i $ (EvilString str) ] (makeparam xs (i+1))
                        makeparam ((Const n):xs) i =
                                flipAfter5 i [param i $ (Literal n)] (makeparam xs (i+1))
                        makeparam ys i = case ys of
                                  (x:xs) -> (mapExprToAsm x) ++ [param i R12] ++ makeparam xs (i+1)
                                  [] -> []
                        flipAfter5 i a b
                                | i > 5      = (b ++ a)
                                | otherwise  = (a ++ b)
                        param i dtsrc = case i of
                                0 -> (Mov' dtsrc RDI)
                                1 -> (Mov' dtsrc RSI)
                                2 -> (Mov' dtsrc RDX)
                                3 -> (Mov' dtsrc RCX)
                                4 -> (Mov' dtsrc R8)
                                5 -> (Mov' dtsrc R9)
                                otherwise -> (Push' dtsrc)



-- -- Skeleton code for santiago --- asm conversion
-- ===================================================

-- Converts regular statements to the pseudo-asm code
-- -- Need newtype because the type needs to be made instance of R12astNode

-- -- converts branching statements to a branch seq of asm ops and
-- -- possibly some additional preamble.  probably will want to return
-- -- ([], BranchSeq <stuff>)
mapBranchToAsm :: BlockId-> ZLast BranchingStatement -> ([ProtoASM], ZLast ProtoBranch)
mapBranchToAsm bid (LastOther (IfBranch expr bid1 bid2))  
	= ([], LastOther $ If' (expressed++[(Cmp' R12 (Literal 0)),(Je' bid2)]) [bid1, bid2])
	where expressed = mapExprToAsm expr
mapBranchToAsm bid (LastOther (Jump bid1))  = ([], LastOther $ Jump' [Jmp' bid1] bid1)
mapBranchToAsm bid (LastOther (WhileBranch expr bid1 bid2))  
	= ([], LastOther $ While' (expressed++[(Cmp' R12 (Literal 0)),(Je' bid2)]) [bid1, bid2])
	where expressed = mapExprToAsm expr
mapBranchToAsm bid (LastExit) = ([],LastExit)
-- Pretty Printing
instance PrettyPrint ProtoASM where
	ppr asm = case asm of 
                (Sub' x y)       -> binop "SUB" x y
                (Add' x y)       -> binop "ADD" x y
                (Mul' x y)       -> binop "MUR12" x y
                (Div' x y)       -> binop "DIV" x y
                (And' x y)       -> binop "AND" x y
                (Or' x y)        -> binop "OR" x y
                (Lt' x y)        -> binop "R12T" x y
                (Gt' x y)        -> binop "GT" x y
                (Le' x y)        -> binop "R12E" x y
                (Ge' x y)        -> binop "GE" x y
                (Ne' x y)        -> binop "NE" x y
                (Eq' x y)        -> binop "EQ" x y
                (Not' x )        -> uniop "NOT" x
                (Neg' x)         -> uniop "NEG" x
                (Mov' x y)	 -> binop "MOV" x y
                (Cmp' x y)	 -> binop "CMP" x y
                (Je' x)	 	 -> uniop "JE" x 
                (Push' x) 	 -> uniop "PUSH" x 
                (Pop' x) 	 -> uniop "PO" x 
                (Call' x) 	 -> text ("CALL "++x)
                (Dec' x) 	 -> uniop "DEC" x 
		_ 		 -> Debug.Trace.trace ("!ppr!!!" ++ (show asm)) (text "@@")
	  where 
  	    binop name x y = text (name++" ") <+> (ppr x) <+> text"," <+> (ppr y) 
	    uniop name x  = text (name++" " )<+> (ppr x)  

instance PrettyPrint Value where
	ppr x = case x of 
		(Symbol str) 		-> text str 
		(Array str i) 		-> text (str ++ "[") <+> ppr i <+> text "]"
		(Literal i)		-> text $ show i
		(EvilString str) 	-> text $ show str
		(R12) 			-> text "R12"
		(R13)			-> text "R13"
		_ 			-> text (show x)


instance PrettyPrint ProtoBranch where
    ppr (Jump' _ bid) = text "Jump" <+> ppr bid
    ppr (If' e [bid1, bid2]) = text "If" <+> parens (hsep $ map ppr  e) <+>
                                 text "then:" <+> ppr bid1 <+>
                                 text "else:" <+> ppr bid2
    ppr (While' e [bid1,bid2]) = text "While" <+> parens (hsep$ map ppr e) <+>
                                 text "loop:" <+> ppr bid1 <+>
				 text "end:" <+> ppr bid2 

{--toR12owIR = lowIRProg


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
