{-# LANGUAGE DeriveDataTypeable #-}
module LowIR where 

import Varmarker
import MidIR
import MonadUniqueEnv
import Control.Monad
import Control.Monad.State
import qualified Data.Map as M
import Data.Generics
import qualified Transforms 
import ControlFlowGraph
import CFGConstruct
import CFGConcrete
import PrettyPrint
import Text.PrettyPrint.HughesPJ hiding (Str)
import Debug.Trace
import Data.Set (Set)
import qualified Data.Set as Set

data Value = Symbol {name::String} | Array {name::String ,index::Value} | Literal Int | EvilSymbol String | EvilString{getString::String} | Label String | Dereference  Value Value | Verbatim String | Stack Int
		| RAX | RBX | RCX | RDX | RSP | RBP | RSI | RDI | R8 | R9 | R10 | R11 
		| R12 | R13 | R14 | R15 | Scoped {getScope::[Scoped] , getValue::Value}
		deriving (Show,Eq,Ord,Data,Typeable)

colorToValue :: Color -> Value
colorToValue CRAX = RAX
colorToValue CRBX = RBX
colorToValue CRCX = RCX
colorToValue CRDX = RDX
colorToValue CRSP = RSP
colorToValue CRBP = RBP
colorToValue CRSI = RSI
colorToValue CRDI = RDI
colorToValue CR8 = R8
colorToValue CR9 = R9
colorToValue CR10 = R10
colorToValue CR11 = R11
colorToValue CR12 = R12
colorToValue CR13 = R13
colorToValue CR14 = R14
colorToValue CR15= R15

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
	| Div' Value
	| Mod' Value
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
	deriving (Show,Eq,Ord,Data,Typeable)

saveFrame = [RBX, RSP, RBP, R11,R10,R12,R13,R14,R15] 
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
	deriving (Show,Eq,Ord,Data,Typeable)

allNonArrayVarsForLowCfg  :: (Data m, Data l) => LGraph m l -> Set VarMarker
allNonArrayVarsForLowCfg = everything Set.union (Set.empty `mkQ` scopedValToVMSet)

scopedValToVMSet :: Value -> Set VarMarker
scopedValToVMSet v = Set.filter isScoped (valToVMSet v)

valToVMSet :: Value -> Set VarMarker
valToVMSet v = Set.filter isScoped $ valToVMSet' v

valsIndicesToVMSet :: [Value] -> Set VarMarker
valsIndicesToVMSet vals = foldl Set.union Set.empty $ map valIndicesToVMSet vals


valIndicesToVMSet :: Value -> Set VarMarker
valIndicesToVMSet (Array s v) = valToVMSet' v
valIndicesToVMSet (Scoped scp v) = Set.map (setScope scp) $ valIndicesToVMSet v
valIndicesToVMSet _ = Set.empty

valToVMSet' (Symbol s) = Set.singleton $ VarMarker s Transforms.Single []
valToVMSet' (Array s _) = Set.singleton $ VarMarker s (Transforms.Array 0) []
valToVMSet' yada@(Scoped scp v) = Set.map (setScope scp) $ valToVMSet' v
valToVMSet' RAX  = Set.singleton $ Precolored CRAX
valToVMSet' RBX  = Set.singleton $ Precolored CRBX
valToVMSet' RCX  = Set.singleton $ Precolored CRCX
valToVMSet' RDX  = Set.singleton $ Precolored CRDX
valToVMSet' RSP  = Set.singleton $ Precolored CRSP
valToVMSet' RBP  = Set.singleton $ Precolored CRBP
valToVMSet' RSI  = Set.singleton $ Precolored CRSI
valToVMSet' RDI  = Set.singleton $ Precolored CRDI
valToVMSet' R8  = Set.singleton $ Precolored CR8
valToVMSet' R9  = Set.singleton $ Precolored CR9
valToVMSet' R10  = Set.singleton $ Precolored CR10
valToVMSet' R11  = Set.singleton $ Precolored CR11
valToVMSet' R12  = Set.singleton $ Precolored CR12
valToVMSet' R13  = Set.singleton $ Precolored CR13
valToVMSet' R14  = Set.singleton $ Precolored CR14
valToVMSet' R15  = Set.singleton $ Precolored CR15
valToVMSet' _ = Set.empty

valsToVMSet :: [Value] -> Set VarMarker
valsToVMSet vals = foldl Set.union Set.empty $ map valToVMSet vals

usesVariable :: (Data a) => a -> VarMarker -> Bool
usesVariable x vm = everything (||) (False `mkQ` (selectVarByName vm)) x

replaceValinStmt :: (Data a) => VarMarker -> Value -> a -> a
replaceValinStmt vm repVal = everywhere (mkT (replaceValWithVal vm repVal))

replaceValWithVal :: VarMarker -> Value -> Value -> Value
replaceValWithVal vm repVal val = case val == vmToVal vm of
    True -> repVal
    False -> val

vmToVal :: VarMarker -> Value
vmToVal (VarMarker s Transforms.Single scp) = Scoped scp (Symbol s)
-- TODO: Is this correct behavior? Dont have enough info to reconstruct
vmToVal (VarMarker s (Transforms.Array _) scp) = Scoped scp (Array s (Literal 0))
vmToVal (Precolored CRAX) = RAX  
vmToVal (Precolored CRBX) = RBX  
vmToVal (Precolored CRCX) = RCX  
vmToVal (Precolored CRDX) = RDX  
vmToVal (Precolored CRSP) = RSP  
vmToVal (Precolored CRBP) = RBP  
vmToVal (Precolored CRSI) = RSI  
vmToVal (Precolored CRDI) = RDI  
vmToVal (Precolored CR8) = R8  
vmToVal (Precolored CR9) = R9  
vmToVal (Precolored CR10) = R10  
vmToVal (Precolored CR11) = R11  
vmToVal (Precolored CR12) = R12  
vmToVal (Precolored CR13) = R13  
vmToVal (Precolored CR14) = R14  
vmToVal (Precolored CR15) = R15  

selectVarByName :: VarMarker -> Value -> Bool
selectVarByName vm val = val == vmToVal vm

maxStackOffsetForFunction :: (Data a) => String -> a -> Int
maxStackOffsetForFunction fName struct = ((-1)*) $ (maximum $ functionStackOffsets struct) `div` 8
    where functionStackOffsets = everything (++) ([] `mkQ` (selectStackOffset fName))

selectStackOffset :: String -> Value -> [Int] 
selectStackOffset fName (Scoped scope (Stack i)) = case (Func fName) `elem` scope of
    True -> [i]
    False -> []
selectStackOffset _ _ = []

setStacksizeForFunction :: (LastNode l, Data l) => String -> LGraph ProtoASM l -> LGraph ProtoASM l
setStacksizeForFunction fName lgraph = mapLGraphNodes mMap lMap lgraph
    where mMap (BID fName) (Enter' _) = [Enter' correctSize]
          mMap bid other = [other]
          lMap _ zl = (([],[]), zl)
          correctSize = maxStackOffsetForFunction fName lgraph

autoSetFunctionStackSpace :: LGraph ProtoASM ProtoBranch -> LGraph ProtoASM ProtoBranch
autoSetFunctionStackSpace lgraph = foldr setStacksizeForFunction lgraph (allFunctionNames lgraph)

-- Soooo type safe...
allFunctionNames :: LGraph ProtoASM ProtoBranch -> [String]
allFunctionNames lgraph = res
    where bid = lgEntry lgraph
          block = case M.lookup bid (lgBlocks lgraph) of
              Nothing -> error "Malformed Control Flow Graph"
              Just b -> b
          blockList = case getZLast block of
                (LastOther (InitialBranch' bList)) -> bList
                _ -> error "Malformed CFG entry block"
          res = map getStr blockList


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

mkTemp :: Integer -> Value
mkTemp i = (Scoped [Temp] (Symbol $ "t" ++ show i))

-- freshTemp :: UniqStringEnv Value
-- freshTemp = freshTemp' >> lastTemp
-- freshTemp' = do
--     i <- M.findWithDefault 0 "t" uMap
--     return (Scoped [Temp] (Symbol $ temp ))

type Uniq a = UniqCounter a

fresh :: Uniq Integer
fresh = fresh' >> peek
fresh' = do
    uMap <- get
    let i = M.findWithDefault 0 0 uMap
    modify (M.insert 0 (i+1))
    return (i `mod` 1)

freshTemp = liftM mkTemp fresh
lastTemp = liftM mkTemp peek

peek :: Uniq Integer
peek = do
    uMap <- get
    let i = M.findWithDefault 0 0 uMap
    return (i `mod` 1)

-- lastTemp :: UniqCounter Value
-- lastTemp = do
--     uMap <- get
--     let i = M.findWithDefault 0 "t" uMap
--     return $ mkTemp i

type LowCFG = LGraph ProtoASM ProtoBranch

--toLowIRCFG :: ControlFlowGraph -> LowCFG
toLowIRCFG cfg = removeUniqEnv $ mapLGraphNodesM mapStmtToAsm mapBranchToAsm cfg

-- Converts regular statements to the pseudo-asm code
mapStmtToAsm ::BlockId -> Statement -> UniqCounter [ProtoASM]
mapStmtToAsm bid x = case x of
        (Set var expr) -> do
            exprAsm <- mapExprToAsm expr
            assign <- mapVarToValue var
            return $ exprAsm ++ assign
        (DVar (Var str))-> return [Dec' (Symbol str)]
        (DVar (Scopedvar scp (Var str)))-> return [Dec' $ Scoped scp (Symbol str)]
        (DVar (Varray str (Const i)))-> return [Dec' (Array str (Literal i))]
        (DVar (Scopedvar scp (Varray str (Const i))))-> return [Dec' $ Scoped scp (Array str (Literal i))]

        (DFun name ps body)-> freshTemp >>= (\temp -> return $ [DFun' name $ map (Symbol . symbol) ps] ++
				(map (\(x,y) ->(Mov' y x))(zip (map vartoval (take 6 ps)) (reverse [R9, R8, RCX, RDX, RSI, RDI]))) ++ 
                (concatMap (\(i,x) -> [(Mov' (Stack i) temp),(Mov' temp x)]) $ zip [16,24..] $ map vartoval (drop 6 ps)))

        (Callout str param)-> protoMethodCall (FuncCall str param)
        (Function name param) -> protoMethodCall (FuncCall name param)
        Break -> return [Break']-- santiago is a fucking idiot handleBreak branch 
        Continue -> return [Continue'] -- santiago is a fucking idiot handleContinue branch  
        (Return expr) -> do
            exprAsm <- mapExprToAsm expr
            res <- lastTemp
            return $ exprAsm ++[Mov' res RAX, Ret']
        _ -> Debug.Trace.trace ("!!STMT!" ++ (show x)) $ return []
   where vartoval (Var str) = (Symbol str)
         vartoval (Scopedvar scp (Var str)) = (Scoped scp (Symbol str))
-- failure here indicates a lastexit is thrown meaning that a break and continue
-- are not in kosher locations. Should have not passed semantic check!
--	 handleBreak:: ZLast BranchingStatement -> [ProtoASM]
--	 handleBreak (LastOther (WhileBranch _ b1 b2)) = [(Jmp' b1)]
--	 handleBreak (LastOther (Jump b1)) = [(Jmp' b1)]
--	 handleBreak x = Debug.Trace.trace ("ODD!" ++ (show x)) []
--	 handleContinue (LastOther (WhileBranch _ b1 b2)) = [(Jmp' b2)]
--	 handleContinue (LastOther (Jump b1)) = [(Jmp' b1)]

mapVarToValue :: Variable -> UniqCounter [ProtoASM]
mapVarToValue (Var str) = lastTemp >>= (\res -> freshTemp >> return [Mov' res (Symbol str)])
mapVarToValue (Varray str expr) = do  
        res1 <- lastTemp
        exprAsms <- mapExprToAsm expr
        res2 <- lastTemp
        return $ exprAsms ++ [Mov' res1 (Array str res2)]

mapVarToValue (Scopedvar scp (Var str)) = lastTemp >>= (\res -> freshTemp >> return [Mov' res (Scoped scp $Symbol str)])

mapVarToValue (Scopedvar scp (Varray str expr)) = do
    res1 <- lastTemp
    exprAsm <- mapExprToAsm expr
    res2 <- lastTemp
    return $ exprAsm ++ [Mov' res1 (Scoped scp $ Array str res2)]

mapVarToValue x = Debug.Trace.trace ("!!VAR!" ++ (show x)) $ return [Mov' (Symbol "OHFUCK") (Symbol "ERROR")]

mapExprToAsm::Expression -> UniqCounter [ProtoASM]
mapExprToAsm xet = case xet of
                (Sub x y)       -> binop (Sub') y x
                (Add x y)       -> binop (Add') x y
                (Mul x y)       -> binop (Mul') x y
                (Div x y)       -> idiv x y
                (Mod x y)       -> imod x y
                (And x y)       -> binop (And') x y
                (Or x y)        -> binop (Or') x y
                (Lt x y)        -> comparison (CMovl') x y
                (Gt x y)        -> comparison (CMovg') x y
                (Le x y)        -> comparison (CMovle') x y
                (Ge x y)        -> comparison (CMovge') x y
                (Ne x y)        -> comparison (CMovne') x y
                (Eq x y)        -> comparison (CMove') x y
                (Not x )        -> uniop (Not') x
                (Neg x)         -> uniop (Neg') x
                (Const i)       -> freshTemp >>= (\t -> return [Mov' (Literal i) t])
                (Loc (Var x))   -> freshTemp >>= (\t -> return [Mov' (Symbol x) t])
                (Loc (Scopedvar scp (Var x)))   -> freshTemp >>= (\t -> return [Mov' (Scoped scp (Symbol x)) t])

                (Loc (Varray x i))-> do
                    pi <- process i
                    res <- lastTemp
                    ret <- freshTemp
                    return $ pi ++ [Mov' (Array x res) ret]

                (Loc (Scopedvar scp (Varray x i)))-> do
                    pi <- process i
                    res <- lastTemp
                    ret <- freshTemp
                    return $ pi ++ [Mov' (Scoped scp (Array x res)) ret]

                (Str str)       -> freshTemp >>= (\t -> return [Mov' (EvilString str) t])

                (FuncCall n p )	-> do
                    asms <- protoMethodCall xet
                    ret <- freshTemp
                    return $ asms ++ [Mov' RAX ret]

                _ 	-> Debug.Trace.trace ( "!EXPR!!" ++ (show xet)) $ return []
                where
                        binop op x y = do
                            px <- process x
                            res1 <- lastTemp
    --                        freshTemp
                            py <- process y
                            res2 <- lastTemp
                            ret <- freshTemp
                            return $ px ++ py ++ [ Mov' res2 ret, 
                                                  op res1 ret] 
                        uniop op x = do
                            px <- process x
                            res <- lastTemp
                            ret <- freshTemp
                            return $ px ++ [Mov' res ret, op ret]

                        process = mapExprToAsm

                        comparison op x y = do
                            px <- process x
                            res1 <- lastTemp
--			    freshTemp
                            py <- process y
                            res2 <- lastTemp
--			    freshTemp
                            tmp <- freshTemp
--			    freshTemp
                            ret <- freshTemp
                            return $ px ++ py ++ [Cmp' res2 res1,
                                                  Mov' (Literal 0) ret,
                                                  Mov' (Literal 1) tmp,
                                                  op tmp ret]
                        imod y x = do
                                 px <- process x
                                 res1 <- lastTemp
                                 py <- process y
                                 res2 <- lastTemp
                                 tmp1 <- freshTemp
                                 tmp2 <- freshTemp
                                 ret <- freshTemp
                                 return $ px ++ py ++ [ Mov' RAX tmp1,
                                                        Mov' RDX tmp2,
                                                        Mov' (Literal 0) RDX,
                                                        Mov' res2 RAX,
                                                        Div' res1,
                                                        Mov' RDX ret,
                                                        Mov' tmp1 RAX,
                                                        Mov' tmp2 RDX ]
                        idiv y x = do
                                 px <- process x
                                 res1 <- lastTemp
                                 py <- process y
                                 res2 <- lastTemp
                                 tmp1 <- freshTemp
                                 tmp2 <- freshTemp
                                 ret <- freshTemp
                                 return $ px ++ py ++ [ Mov' RAX tmp1,
                                                        Mov' RDX tmp2,
                                                        Mov' (Literal 0) RDX,
                                                        Mov' res2 RAX,
                                                        Div' res1,
                                                        Mov' RAX ret,
                                                        Mov' tmp1 RAX,
                                                        Mov' tmp2 RDX ]

protoMethodCall:: Expression -> UniqCounter [ProtoASM]
protoMethodCall (FuncCall name midParam) = do
    params <- makeparam midParam 0
    return $ save
        ++ params
        ++ (if name == "printf" then [Mov' (Literal 0) RAX] else [])
--	++ reverse ( take (minimum [6,(length midParam)]) ( reverse [(Pop' R9),(Pop' R8),(Pop' RCX),(Pop' RDX),(Pop' RSI),(Pop' RDI)]))
        ++ [Call' name]
        ++ [(Pop' RBX) | x<- [1..((length midParam) - 6)]]
    	++ restore
                where   params =  makeparam midParam 0
                        makeparam ((Str str):xs) i = do
                            p <- makeparam xs (i+1)
                            return $ flipAfter5 i [param i $ (EvilString str) ] p
                        makeparam ((Const n):xs) i = do
                            p <- makeparam xs (i+1)
                            return $ flipAfter5 i [param i $ (Literal n)] p
                        makeparam ys i = case ys of
                                  (x:xs) -> do
                                      expressed <- mapExprToAsm x 
                                      tmp <- lastTemp
                                      p <- makeparam xs (i+1)
                                      return $ expressed ++ [param i tmp] ++ p
                                  [] -> return []
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

mapBranchToAsm :: BlockId-> ZLast BranchingStatement -> UniqCounter (([ProtoASM],[ProtoASM]), ZLast ProtoBranch)
mapBranchToAsm bid (LastOther (IfBranch expr bid1 bid2))  
	= do
        expressed <- mapExprToAsm expr
        tmp <- lastTemp
        return $ (([],expressed++[Cmp' (Literal 0) tmp,Je' bid2]), LastOther $ If' [] [bid1, bid2])

mapBranchToAsm bid (LastOther (Jump bid1))  = return $ (([],[Jmp' bid1]), LastOther $ Jump' bid1)
mapBranchToAsm bid (LastOther (WhileBranch expr bid1 bid2))  
	= do
        expressed <- mapExprToAsm expr
        tmp <- lastTemp
        return $ (([],expressed++[(Cmp' (Literal 0) tmp),(Je' bid2)]), LastOther $ While' [] [bid1, bid2])

mapBranchToAsm bid (LastOther (ForBranch v@(Var str) startexpr expr bid1 bid2))  
	= do
        expressed <- mapExprToAsm expr
	endtmp <- lastTemp
        return $ ((expressed ++ [(Cmp' (Symbol str) endtmp),(Je' bid2)],[]), LastOther $ For' (Literal 0) [] [] [] [bid1, bid2])

mapBranchToAsm bid (LastOther (ParaforBranch (Var str) startexpr expr bid1 bid2))  
	= do
        expressed <- mapExprToAsm expr
        tmp <- lastTemp
        return $ (([], expressed ++[(Cmp' (Symbol str) tmp),(Je' bid2)]), LastOther $ Parafor' (Literal 0) [] [] [] [bid1, bid2])

mapBranchToAsm bid (LastOther (ForBranch  v@(Scopedvar scp (Var str)) startexpr expr bid1 bid2))  
	= do
       -- sExpressed <- mapExprToAsm startexpr
	--vExpr <- mapVarToValue v
        expressed <- mapExprToAsm expr
	endtmp <- lastTemp
	
       -- sExpressed' <- mapExprToAsm startexpr
        -- tmp <- Debug.Trace.trace "fasfadfa1231312" lastTemp 
        return $ (([], expressed ++ [(Cmp' (Scoped scp (Symbol str)) endtmp),(Je' bid2)]), LastOther $ For' (Literal 0) []  [] [] [bid1, bid2])

mapBranchToAsm bid (LastOther (ParaforBranch (Scopedvar scp (Var str)) startexpr expr bid1 bid2))  
	= do
        expressed <- mapExprToAsm expr
        sExpressed <- mapExprToAsm startexpr
        tmp <- lastTemp
        return $ (([], expressed ++ [(Cmp' (Scoped scp (Symbol str)) tmp),(Je' bid2)]), LastOther $ Parafor' (Literal 0) sExpressed  expressed [] [bid1, bid2])




mapBranchToAsm bid (LastOther (InitialBranch bids)) = return (([],[]), (LastOther (InitialBranch' bids)))

mapBranchToAsm bid (LastExit) = return (([],[]),LastExit)


-- Pretty Printing
instance PrettyPrint ProtoASM where
	ppr asm = case asm of 
                (Sub' x y)       -> binop "sub" x y
                (Add' x y)       -> binop "add" x y
                (Mul' x y)       -> binop "imul" x y
                (Div' x)         -> uniop "idiv" x 
                (And' x y)       -> binop "and" x y
                (Or' x y)        -> binop "or" x y
                (DFun' name params)        -> text "# Function Declaration: " <> text name
                (Not' x )        -> uniop "not" x
                (Neg' x)         -> uniop "neg" x
                (Mov' x y)	 -> binop "movq" x y
                (Cmp' x y)	 -> binop "cmp"  x y --hack please dont bite back
                (CMove' x y)	 -> binop "cmove" x y
                (CMovne' x y)	 -> binop "cmovne" x y
                (CMovg' x y)	 -> binop "cmovg" x y
                (CMovge' x y)	 -> binop "cmovge" x y
                (CMovl' x y)	 -> binop "cmovl" x y
                (CMovle' x y)	 -> binop "cmovle" x y
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
	    uniop name x  = text name <+> (ppr x)  
  	    binop name x y = text (name++" ") <+> (ppr x) <+> text"," <+> (ppr y) 

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
            Scoped scope (Symbol str) -> ppr (Symbol (namifyy' scope str))
            Scoped scope (Array str i) -> ppr (Array (namifyy' scope str) i)
            Scoped scope vy@(Scoped _ _) -> ppr vy
            _ 			-> text (show x)


--namifyy (Scoped scope y) = namifyy' scope y
namifyy' (s:ss) y'
        | Global  <- s = "global_" ++ namifyy' ss y'
        | Func st <- s = st ++ "_" ++ namifyy' ss y'
        | Loop st <- s = st ++ "_" ++ namifyy' ss y'
namifyy' _ y' =  y'



instance PrettyPrint ProtoBranch where
    ppr (Jump' bid) = text "" --text "mp" <+> ppr bid
    ppr (If' stmts _) = vcat $ map ppr stmts
    ppr (While' stmts _) = text ""--vcat $ map ppr stmts
    ppr (For' _ _ _ stmts _) = text ""--vcat $ map ppr stmts
    ppr (Parafor' _  _ _ stmts _) = text ""--vcat $ map ppr stmts
    ppr (InitialBranch' bids) = text "# Methods Defined:" <+> hsep (map ppr bids)

