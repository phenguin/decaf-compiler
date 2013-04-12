module LowIR where 

import MidIR
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
	| DFun' String [Value]
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
	| Pop' Value
	| Push' Value
        | CMove' Value Value 
        | CMovne' Value Value 
        | CMovg' Value Value 
        | CMovl' Value Value 
        | CMovge' Value Value 
        | CMovle' Value Value 
        | Jmp' BlockId
        | Jle' BlockId
        | Jl' BlockId
        | Jge' BlockId
        | Jne' BlockId
	deriving (Show,Eq,Ord)

saveFrame = [RBX, RSP, RBP, R12,R13,R14,R15] 
save::[ProtoASM]
save	= map Push' saveFrame
restore::[ProtoASM]
restore = map Pop' (reverse saveFrame)

data ProtoBranch =  Jump' BlockId
	| If' [ProtoASM] [BlockId]
	| While' [ProtoASM] [BlockId]
	| InitialBranch' [BlockId]
	deriving (Show,Eq,Ord)

newtype ProtoASMList = ProtoASMList [ProtoASM]

instance PrettyPrint ProtoASMList where
    ppr (ProtoASMList bs) = text "<End Block>" $$ text "Branch Targets:" <+> (hsep $ map ppr bs) $$ text ""


instance HavingSuccessors ProtoBranch where
	succs x = case x of
		(Jump' b1) 	-> [b1]
		(If' _ x) 	-> x
		(While' _ x)    -> x
		(InitialBranch' bids)    -> bids

instance LastNode ProtoBranch where
	mkBranchNode bid = Jump' bid
	isBranchNode s = case s of
		Jump' _ 	-> True
		_ 	-> False


--newtype CSEnv = Data.Map.Map  Expression Expression

--cse:: ControlFlowGraph -> Either a [IO()]


type LowCFG = LGraph ProtoASM ProtoBranch

toLowIRCFG :: ControlFlowGraph -> LowCFG
toLowIRCFG cfg = mapLGraphNodes (mapStmtToAsm) (mapBranchToAsm) cfgLGraph
      where cfgLGraph = lgraphSpanningFunctions cfg

-- Converts regular statements to the pseudo-asm code
mapStmtToAsm :: BlockId -> Statement -> [ProtoASM]
mapStmtToAsm bid x = case x of
        (Set var expr) -> (mapExprToAsm expr) ++ [Mov' R12 R14] ++ (mapVarToValue var) ++
			[Mov' R14 R12]
        (DVar (Var str))-> [Dec' (Symbol str)]
        (DVar (Varray str (Const i)))-> [Dec' (Array str (Literal i))]
        (DFun name ps body)-> [DFun' name $ map (Symbol . symbol) ps]
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
mapBranchToAsm :: BlockId-> ZLast BranchingStatement -> (([ProtoASM],[ProtoASM]), ZLast ProtoBranch)
mapBranchToAsm bid (LastOther (IfBranch expr bid1 bid2))  
	= (([],[]), LastOther $ If' (expressed++[(Cmp' R12 (Literal 0)),(Je' bid2)]) [bid1, bid2])
	where expressed = mapExprToAsm expr

mapBranchToAsm bid (LastOther (Jump bid1))  = (([],[]), LastOther $ Jump' bid1)
mapBranchToAsm bid (LastOther (WhileBranch expr bid1 bid2))  
	= (([],[]), LastOther $ While' (expressed++[(Cmp' R12 (Literal 0)),(Je' bid2)]) [bid1, bid2])
	where expressed = mapExprToAsm expr

mapBranchToAsm bid (LastOther (InitialBranch bids)) = (([],[]), (LastOther (InitialBranch' bids)))

mapBranchToAsm bid (LastExit) = (([],[]),LastExit)

-- Pretty Printing
instance PrettyPrint ProtoASM where
	ppr asm = case asm of 
                (Sub' x y)       -> binop "sub" x y
                (Add' x y)       -> binop "add" x y
                (Mul' x y)       -> binop "mul" x y
                (Div' x y)       -> binop "div" x y
                (And' x y)       -> binop "and" x y
                (Or' x y)        -> binop "or" x y
                (Lt' x y)        -> binop "lt" x y
                (Gt' x y)        -> binop "gt" x y
                (Le' x y)        -> binop "le" x y
                (Ge' x y)        -> binop "ge" x y
                (Ne' x y)        -> binop "ne" x y
                (Eq' x y)        -> binop "eq" x y
                (DFun' name params)        -> text "# Function Declaration: " <> text name
                (Not' x )        -> uniop "not" x
                (Neg' x)         -> uniop "neg" x
                (Mov' x y)	 -> binop "mov" x y
                (Cmp' x y)	 -> binop "cmp" x y
                (Je' x)	 	 -> uniop "je" x 
                (Push' x) 	 -> uniop "push" x 
                (Pop' x) 	 -> uniop "pop" x 
                (Call' x) 	 -> text ("call "++x)
                (Dec' x) 	 -> text ""
		_ 		 -> Debug.Trace.trace ("!ppr!!!" ++ (show asm)) (text "@@")
	  where 
  	    binop name x y = text (name++" ") <+> (ppr x) <+> text"," <+> (ppr y) 
	    uniop name x  = text (name++" " )<+> (ppr x)  

instance PrettyPrint Value where
	ppr x = case x of 
            (Symbol str) 		-> text str 
            (Array str i) 		-> text (str ++ "[") <+> ppr i <+> text "]"
            (Literal i)		-> text $"$" ++ ( show i)
            (EvilString str) 	-> text $ show str
            RAX -> text "%rax"
            RBX -> text "%rbx"
            RCX -> text "%rcx"
            RDX -> text "%rdx"
            RSP -> text "%rsp"
            RBP -> text "%rbp"
            RSI -> text "%rsi"
            RDI -> text "%rdi"
            R8 ->  text "%r8"
            R9 ->  text "%r9"
            R10 -> text "%r10"
            R11 -> text "%r11"
            R12 -> text "%r12"
            R13 -> text "%r13"
            R14 -> text "%r14"
            R15 -> text "%r15"
            _ 			-> text (show x)


instance PrettyPrint ProtoBranch where
    ppr (Jump' bid) = text "Jmp" <+> ppr bid
    ppr (If' stmts _) = vcat $ map ppr stmts
    ppr (While' stmts _) = text ""--vcat $ map ppr stmts
    ppr (InitialBranch' bids) = text "# Methods Defined:" <+> hsep (map ppr bids)

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
