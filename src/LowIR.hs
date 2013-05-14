module LowIR where 





import MidIR
import qualified Data.Map 
import ControlFlowGraph
import CFGConstruct
import CFGConcrete
import PrettyPrint
import Text.PrettyPrint.HughesPJ hiding (Str)
import Debug.Trace

data Value = Symbol {name::String} | Array {name::String ,index::Value} | Literal Int | EvilSymbol String | EvilString{getString::String} | Label String | Dereference  Value Value | Verbatim String | Stack Int
		| RAX | RBX | RCX | RDX | RSP | RBP | RSI | RDI | R8 | R9 | R10 | R11 
		| R12 | R13 | R14 | R15 | Scoped {getScope::[Scoped] , getValue::Value}
		deriving (Show,Eq,Ord)

isRegister x = elem x [RAX ,RBX,RCX,RDX,RSP,RBP,RSI,RDI,R8,R9,R10,R11,R12,R13,R14,R15]	
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
	| Enter' Int
	| Ret'
	| Break'    -- get replaced with jump later... kludgy i know
	| Continue' -- get replaced with jump later... kludgy i know
	deriving (Show,Eq,Ord)

saveFrame = [RBX, RSP, RBP, R12,R13,R14,R15] 
save::[ProtoASM]
save	= map Push' saveFrame
restore::[ProtoASM]
restore = map Pop' (reverse saveFrame)

data ProtoBranch =  Jump' BlockId
	| If' [ProtoASM] [BlockId]
	| While' [ProtoASM] [BlockId]
	| For' Value [ProtoASM] [ProtoASM] [ProtoASM] [BlockId]
	| Parafor' Value [ProtoASM] [ProtoASM] [ProtoASM] [BlockId]
	| InitialBranch' [BlockId]
	| Nil --for stateful traversion
	deriving (Show,Eq,Ord)

newtype ProtoASMList = ProtoASMList [ProtoASM]

instance PrettyPrint ProtoASMList where
    ppr (ProtoASMList bs) = text "<End Block>" $$ text "Branch Targets:" <+> (hsep $ map ppr bs) $$ text ""


instance HavingSuccessors ProtoBranch where
	succs x = case x of
		(Jump' b1) 	-> [b1]
		(If' _ x) 	-> x
		(While' _ x)    -> x
		(For' _ _ _ _ x)    -> x
		(Parafor' _ _ _ _ x)    -> x
		(InitialBranch' bids)    -> bids

instance LastNode ProtoBranch where
	mkBranchNode bid = Jump' bid
	isBranchNode s = case s of
		Jump' _ 	-> True
		_ 	-> False


--newtype CSEnv = Data.Map.Map  Expression Expression

--cse:: ControlFlowGraph -> Either a [IO()]


type LowCFG = LGraph ProtoASM ProtoBranch

--toLowIRCFG :: ControlFlowGraph -> LowCFG
toLowIRCFG cfg = mapLGraphNodes (mapStmtToAsm) (mapBranchToAsm) cfg

-- Converts regular statements to the pseudo-asm code
mapStmtToAsm ::BlockId -> Statement -> [ProtoASM]
mapStmtToAsm bid x = case x of
        (Set var expr) -> (mapExprToAsm expr) ++ [Mov' (Symbol "t1") (Symbol "t3")] ++ (mapVarToValue var) 
        (DVar (Var str))-> [Dec' (Symbol str)]
        (DVar (Scopedvar scp (Var str)))-> [Dec' $ Scoped scp (Symbol str)]
        (DVar (Varray str (Const i)))-> [Dec' (Array str (Literal i))]
        (DVar (Scopedvar scp (Varray str (Const i))))-> [Dec' $ Scoped scp (Array str (Literal i))]
        (DFun name ps body)-> [DFun' name $ map (Symbol . symbol) ps] ++
				(map (\(x,y) ->(Mov' y x))(zip (map vartoval (take 6 ps)) (reverse [R9, R8, RCX, RDX, RSI, RDI]))) ++ (concatMap (\(i,x) -> [(Mov' (Stack i) (Symbol "t1")),(Mov' (Symbol "t1") x)]) $ zip [16,24..] $ map vartoval (drop 6 ps))

        (Callout str param)-> protoMethodCall (FuncCall str param)
	(Function name param) -> protoMethodCall (FuncCall name param)
	(Break) -> [Break']-- santiago is a fucking idiot handleBreak branch 
	(Continue) -> [Continue'] -- santiago is a fucking idiot handleContinue branch  
	(Return expr) -> (mapExprToAsm expr)++ [Mov' (Symbol "t0") RAX] ++ [Ret']
	_ 	-> Debug.Trace.trace ("!!STMT!" ++ (show x)) []
   where vartoval (Var str) = (Symbol str)
-- failure here indicates a lastexit is thrown meaning that a break and continue
-- are not in kosher locations. Should have not passed semantic check!
--	 handleBreak:: ZLast BranchingStatement -> [ProtoASM]
--	 handleBreak (LastOther (WhileBranch _ b1 b2)) = [(Jmp' b1)]
--	 handleBreak (LastOther (Jump b1)) = [(Jmp' b1)]
--	 handleBreak x = Debug.Trace.trace ("ODD!" ++ (show x)) []
--	 handleContinue (LastOther (WhileBranch _ b1 b2)) = [(Jmp' b2)]
--	 handleContinue (LastOther (Jump b1)) = [(Jmp' b1)]
mapVarToValue (Var str) = [Mov' (Symbol "t3") (Symbol str)]
mapVarToValue (Varray str expr) =   (mapExprToAsm expr) ++ [Mov' (Symbol "t3") (Array str (Symbol "t0"))]
mapVarToValue (Scopedvar scp (Var str)) = [Mov' (Symbol "t3") (Scoped scp $Symbol str)]
mapVarToValue (Scopedvar scp (Varray str expr)) =   (mapExprToAsm expr) ++ [Mov' (Symbol "t3") (Scoped scp $Array str (Symbol "t0"))]
mapVarToValue x = Debug.Trace.trace ("!!VAR!" ++ (show x)) [Mov' (Symbol "OHFUCK") (Symbol "ERROR")]

mapExprToAsm::Expression -> [ProtoASM]
mapExprToAsm xet = case xet of
                (Sub x y)       -> binop (Sub') y x
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
                (Const i)       -> [Mov' (Literal i) (Symbol "t0")]
                (Loc (Var x))   -> [Mov' (Symbol x) (Symbol "t0")]
                (Loc (Scopedvar scp (Var x)))   -> [Mov' (Scoped scp (Symbol x)) (Symbol "t0")]
                (Loc (Varray x i))-> let pi = process i in 
					pi ++ [(Mov' (Symbol "t0") (Symbol "t1")),(Mov' (Array x (Symbol "t1")) (Symbol "t0"))]
                (Loc (Scopedvar scp (Varray x i)))-> let pi = process i in 
					pi ++ [(Mov' (Symbol "t0") (Symbol "t1")),(Mov' (Scoped scp (Array x (Symbol "t1"))) (Symbol "t0"))]
                (Str str)       -> [Mov' (EvilString str) (Symbol "t0")]
		(FuncCall n p )	-> protoMethodCall xet ++ [Mov' RAX (Symbol "t0")]
		_ 	-> Debug.Trace.trace ( "!EXPR!!" ++ (show xet)) []
                where
                        binop t x y = let px = process x
                                          py = process' y in
                                        (px
                                         ++[Mov' (Symbol "t0") (Symbol "t1")]
                                         ++ py
                                         ++ [t (Symbol "t1") (Symbol "t0")])
                        uniop t x  = let px = process x in
                                        (px
                                         ++ [t (Symbol "t0")])
                        process = mapExprToAsm
                        process' = mapExprToAsm'

mapExprToAsm' x = case x of
                (Sub x y)       -> binop (Sub') y x
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
                (Const i)       -> [Mov' (Literal i) (Symbol "t0")]
                (Loc (Var x))   -> [Mov' (Symbol x) (Symbol "t0")]
                (Loc (Scopedvar scp (Var x)))   -> [Mov' (Scoped scp (Symbol x)) (Symbol "t0")]
                (Loc (Varray x i))-> let pi = process i in 
					pi ++ [(Mov' (Symbol "t0") (Symbol "t1")),(Mov' (Array x (Symbol "t1")) (Symbol "t0"))]
                (Loc (Scopedvar scp (Varray x i)))-> let pi = process i in 
					pi ++ [(Mov' (Symbol "t0") (Symbol "t1")),(Mov' (Scoped scp (Array x (Symbol "t1"))) (Symbol "t0"))]
                (Str str)       -> [Mov' (EvilString str) (Symbol "t0")]
		(FuncCall n p )	-> protoMethodCall x ++ [Mov' RAX (Symbol "t0")]
		_ 	-> Debug.Trace.trace ( "!EXPR!!" ++ (show x)) []
                where
                        binop t x y = let px = process x
                                          py = process' y in
                                        (px
                                         ++ [Mov' (Symbol "t0") (Symbol "t4")]
                                         ++ py
                                         ++ [t (Symbol "t4") (Symbol "t0")])
                        uniop t x  = let px = process x in
                                        (px
                                         ++ [t (Symbol "t0")])
                        process = mapExprToAsm
                        process' = mapExprToAsm'


protoMethodCall:: Expression -> [ProtoASM]
protoMethodCall (FuncCall name midParam) =
    	save
        ++ params
        ++ (if name == "printf" then [Mov' (Literal 0) RAX] else [])
--	++ reverse ( take (minimum [6,(length midParam)]) ( reverse [(Pop' R9),(Pop' R8),(Pop' RCX),(Pop' RDX),(Pop' RSI),(Pop' RDI)]))
        ++ [Call' name]
        ++ [(Pop' RBX) | x<- [1..((length midParam) - 6)]]
    	++ restore
                where   params =  makeparam midParam 0
                        makeparam ((Str str):xs) i =
                                flipAfter5 i [param i $ (EvilString str) ] (makeparam xs (i+1))
                        makeparam ((Const n):xs) i =
                                flipAfter5 i [param i $ (Literal n)] (makeparam xs (i+1))
                        makeparam ys i = case ys of
                                  (x:xs) -> (mapExprToAsm x) ++ [param i (Symbol "t0")] ++ makeparam xs (i+1)
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
	= (([],(expressed++[(Cmp' (Literal 0) (Symbol "t0")),(Je' bid2)])), LastOther $ If' [] [bid1, bid2])
--	= (([],[]), LastOther $ If' (expressed++[(Cmp' (Literal 0) R12),(Je' bid2)]) [bid1, bid2])
	where expressed = mapExprToAsm expr

mapBranchToAsm bid (LastOther (Jump bid1))  = (([],[Jmp' bid1]), LastOther $ Jump' bid1)
mapBranchToAsm bid (LastOther (WhileBranch expr bid1 bid2))  
	= (([],expressed++[(Cmp' (Literal 0) (Symbol "t0")),(Je' bid2)]), LastOther $ While' [] [bid1, bid2])
--	= (([],expressed++[(Cmp' (Literal 0) R12),(Je' bid2)]), LastOther $ While' (expressed++[(Cmp' (Literal 0) R12 ),(Je' bid2)]) [bid1, bid2])
	where expressed = mapExprToAsm expr

mapBranchToAsm bid (LastOther (ForBranch (Var str) startexpr expr bid1 bid2))  
	= (([], expressed++[(Cmp' (Symbol str) (Symbol "t0")),(Je' bid2)]), LastOther $ For' (Literal 0) (mapExprToAsm expr) expressed [] [bid1, bid2])
	where expressed = mapExprToAsm expr

mapBranchToAsm bid (LastOther (ParaforBranch (Var str) startexpr expr bid1 bid2))  
	= (([], expressed ++[(Cmp' (Symbol str) (Symbol "t0")),(Je' bid2)]), LastOther $ Parafor' (Literal 0) (mapExprToAsm expr)  expressed [] [bid1, bid2])
	where expressed = mapExprToAsm expr

mapBranchToAsm bid (LastOther (ForBranch (Scopedvar scp (Var str)) startexpr expr bid1 bid2))  
	= (([], expressed++[(Cmp' (Scoped scp (Symbol str)) (Symbol "t0")),(Je' bid2)]), LastOther $ For' (Literal 0) (mapExprToAsm expr) expressed [] [bid1, bid2])
	where expressed = mapExprToAsm expr

mapBranchToAsm bid (LastOther (ParaforBranch (Scopedvar scp (Var str)) startexpr expr bid1 bid2))  
	= (([], expressed ++[(Cmp' (Scoped scp (Symbol str)) (Symbol "t0")),(Je' bid2)]), LastOther $ Parafor' (Literal 0) (mapExprToAsm expr)  expressed [] [bid1, bid2])
	where expressed = mapExprToAsm expr




mapBranchToAsm bid (LastOther (InitialBranch bids)) = (([],[]), (LastOther (InitialBranch' bids)))

mapBranchToAsm bid (LastExit) = (([],[]),LastExit)

-- Pretty Printing
instance PrettyPrint ProtoASM where
	ppr asm = case asm of 
                (Sub' x y)       -> binop "sub" x y
                (Add' x y)       -> binop "add" x y
                (Mul' x y)       -> binop "imul" x y
                (Div' x y)       -> idiv x y
                (And' x y)       -> binop "and" x y
                (Or' x y)        -> binop "or" x y
                (Lt' x y)        -> comparison "cmovl" x y
                (Gt' x y)        -> comparison "cmovg" x y
                (Le' x y)        -> comparison "cmovle" x y
                (Ge' x y)        -> comparison "cmovge" x y
                (Ne' x y)        -> comparison "cmovne" x y
                (Eq' x y)        -> comparison "cmove" x y
                (DFun' name params)        -> text "# Function Declaration: " <> text name
                (Not' x )        -> uniop "not" x
                (Neg' x)         -> uniop "neg" x
                (Mov' x y)	 -> binop "movq" x y
                (Cmp' x y)	 -> binop "cmp" x y
                (Je' x)	 	 -> uniop "je" x 
                (Jne' x)	 -> uniop "jne" x 
                (Push' x) 	 -> uniop "push" x 
                (Pop' x) 	 -> uniop "pop" x 
                (Call' x) 	 -> text ("call "++x)
                (Dec' x) 	 -> text ""
                (Ret') 	 	 -> (text "leave") $$ (text "ret")
                (Jmp' x) 	 -> text ("jmp " ++ getStr x)
                (Enter' x) 	 -> text ("enter $(8*"++(show x)++") , $0 ")
		_ 		 -> Debug.Trace.trace ("!ppr!!!" ++ (show asm)) (text "@@")
	  where 
  	    binop name x y = text (name++" ") <+> (ppr x) <+> text"," <+> (ppr y) 
  	    comparison name x y = text ("cmp"++" ") <+> (ppr y) <+> text"," <+> (ppr x) 
				$$ text ("movq" ++ " $0 , t0")
				$$ text ("movq" ++ " $1 , %rbx")
				$$ text (name ++ " %rbx , t0")
	    uniop name x  = text (name++" " )<+> (ppr x)  
  	    idiv x y =    text "mov %rax , t5"
			$$ text "mov %rdx , t6" 
			$$ text ("mov $0, %rdx") 
			$$ text "mov "<+> (ppr x) <+> text", %rax"
			$$ text "idiv " <+> (ppr y) 
			$$ text "mov %rax, t0 "
			$$ text "mov t5 , %rax"
			$$ text "mov t6 , %rdx"
instance PrettyPrint Value where
	ppr x = case x of 
            (Symbol str) 		-> text $  str   
            (EvilSymbol str) 		-> text $  "$" ++ str   
            (Array str i) 		-> (text $ str++"(,") <+> (ppr i) <+>  text (",8)")
            (Literal i)			-> text $"$" ++ ( show i)
            (EvilString str) 		-> text $ show str
            (Verbatim str) 		-> text $str
            (Dereference x y) 		-> (ppr x) <+> (text "(,") <+>(ppr y) <+>  text (",8)")
	    (Stack i)			-> text $ (show i) ++ "(%rbp)"  
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
    ppr (Jump' bid) = text "" --text "mp" <+> ppr bid
    ppr (If' stmts _) = vcat $ map ppr stmts
    ppr (While' stmts _) = text ""--vcat $ map ppr stmts
    ppr (For' _ _ _ stmts _) = text ""--vcat $ map ppr stmts
    ppr (Parafor' _  _ _ stmts _) = text ""--vcat $ map ppr stmts
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
