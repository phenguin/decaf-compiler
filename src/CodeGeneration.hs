{-# LANGUAGE FlexibleInstances #-}

module CodeGeneration where

import Transforms
import MemoryIRTree
import Control.Monad
import MultiTree
import Semantics
import Data.List
import Data.Char
import Data.Hashable (hash, Hashable)

getHashStr :: (Hashable a) => a -> String
getHashStr x = case h < 0 of
    True -> 'N' : show (abs h)
    False -> 'P' : show h
    where h = hash x

data DataSource = M MemLoc | C Int deriving (Eq) --memory location, or constant (immediate value)

data AsmOp = Mov DataSource MemLoc
         | CMove Register Register 
         | CMovne Register Register 
         | CMovg Register Register 
         | CMovl Register Register 
         | CMovge Register Register 
         | CMovle Register Register 
         | Enter Int
         | Leave
         | Push DataSource
         | Pop MemLoc
         | Call MemLoc
         | Ret
         | Jmp MemLoc
         | Je MemLoc
         | Jne MemLoc
         | AddQ DataSource MemLoc
         | AndQ DataSource MemLoc
         | OrQ DataSource MemLoc
         | XorQ DataSource MemLoc
         | SubQ DataSource MemLoc
         | IMul DataSource MemLoc
         | IDiv DataSource
         | Shr Register
         | Shl Register
         | Ror DataSource MemLoc
         | Cmp DataSource MemLoc
         | Lbl String
         | AsmString String
         deriving (Eq)

instance Show DataSource where
	show (M ml) = show ml
	show (C i) = '$' : show i

instance Show AsmOp where
         show (Mov x y) = "mov "++(show x)++", "++ (show y) 
         show (CMove x y) = "cmove "++(show x)++", "++ (show y) 
         show (CMovne x y) = "cmove "++(show x)++", "++ (show y)
         show (CMovg x y) = "cmovne "++(show x)++", "++ (show y)
         show (CMovl x y) = "cmovl "++(show x)++", "++ (show y)
         show (CMovge x y) = "cmovge "++(show x)++", "++ (show y)
         show (CMovle x y) = "cmovle "++(show x)++", "++ (show y)
         show (Enter x) = "enter "++(show x)
         show Leave = "leave"
         show (Push x) = "push "++(show x)
         show (Pop x) = "pop "++(show x)
         show (Call x) = "call "++(show x)
         show Ret = "ret"
         show (Jmp x) = "jmp "++(show x)
         show (Je x) = "je "++(show x)
         show (Jne x) = "jne "++(show x)
         show (AddQ x y) = "addq "++(show x)++", "++ (show y)
         show (AndQ x y) = "and "++(show x)++", "++ (show y)
         show (OrQ x y) = "or "++(show x)++", "++ (show y)
         show (XorQ x y) = "xor "++(show x)++", "++ (show y)
         show (SubQ x y) = "subq "++(show x)++", "++ (show y)
         show (IMul x y) = "imul "++(show x)++", "++ (show y)
         show (IDiv x) = "idiv "++(show x)
         show (Shr x) = "shr "++(show x)
         show (Shl x) = "shl "++(show x)
         show (Ror x y) = "ror "++(show x)++", "++ (show y)
         show (Cmp x y) = "cmp "++(show x)++", "++ (show y)
         show (Lbl "main") = ".globl main\nmain:"
         show (Lbl x) = x ++ ":"
         show (AsmString s) = ".string " ++ show s

handler:: IRNode -> (LowIRTree -> [AsmOp])
handler node = case node of
            MethodCallL _                ->asmMethodCall
            AndL                         ->asmAnd
            OrL                          ->asmOr
            AddL                         ->asmAdd
            SubL                         ->asmSub
            MulL                         ->asmMul
            ModL                         ->asmMod
            DivL                         ->asmDiv
            NotL                         ->asmNot
            NegL                         ->asmNeg
            AssignPlusL                  ->asmAssignPlus
            AssignMinusL                 ->asmAssignMinus
            AssignL                      ->asmAssign
            NeqlL                        ->asmNeql
            EqlL                         ->asmEql
            LtL                          ->asmLt
            LteL                         ->asmLte
            GtL                          ->asmGt
            GteL                         ->asmGte
            LocL _                       ->asmLoc
            DStrL _                      ->asmDStr
            DCharL _                     ->asmDChar
            DIntL _                      ->asmDInt
            DBoolL _                     ->asmDBool
            DBlockL                      ->asmDBlock
            ReturnL                      ->asmReturn
            BreakL                       ->asmBreak
            ContinueL                    ->asmContinue
            IfL                          ->asmIf
            ForL _                       ->asmFor
            WhileL                       ->asmWhile
        --    FDL _ _                      ->asmFD
         --   CDL _                        ->asmCD
            PDL _                        ->asmPD
            MDL _                        ->asmMD
            ProgL                        ->asmProg
            _                           -> const []

asmTransform:: LowIRTree -> [AsmOp]
asmTransform node@(MT stnode _) = (handler stnode) node

getAssemblyStr :: SemanticTreeWithSymbols -> String
getAssemblyStr node = concat $ intersperse "\n" $ map show $ asmTransform $ convertToLowIRTree node

----- Assembly generation helper functions
ld :: (ValidDataSource a, ValidMemLoc b) => a -> b -> AsmOp
ld x y = Mov (toDataSource x) (toMemLoc y)

class ValidDataSource a where
    toDataSource :: a -> DataSource

instance ValidDataSource DataSource where
    toDataSource = id

instance ValidDataSource Int where
    toDataSource = C

instance ValidDataSource Integer where
    toDataSource = C . fromIntegral

instance ValidDataSource Register where
    toDataSource = M . Reg

instance ValidDataSource MemLoc where
    toDataSource = M

instance Registerizable DataSource where
    reg x = M (reg x)

    isReg (M (Reg _)) = True
    isReg _ = False

    getReg (M (Reg x)) = Just x
    getReg _ = Nothing


asmBinOp :: (Registerizable a, Registerizable b) => (a -> b -> AsmOp) -> LowIRTree -> [AsmOp]
asmBinOp binop node@(MT stnode (t1:t2:ts)) = asmTransform t1 ++ [ld RAX R10] ++ asmTransform t2 ++ [binop (reg R10) (reg RAX)]

asmMethodCall :: LowIRTree -> [AsmOp]
asmMethodCall node@(MT (MethodCallL id) forest) =  
	 params ++ (if idString id == "printf" then [ld (0 :: Int) RAX] else []) ++ [Call (Label (idString id))]
		where 	params =  makeparam forest 0
			makeparam ((MT (DStrL str) _):xs) i =  
				[param i $ toDataSource (Label ("$." ++ (getHashStr str))) ] ++ (makeparam xs (i+1))
			makeparam ((MT (DCharL chrtr) _):xs) i = 
				[param i $ toDataSource (C (ord chrtr)) ] ++ (makeparam xs (i+1))
			makeparam ((MT (DIntL intgr) _):xs) i = 
				[param i $ toDataSource (C intgr) ] ++ (makeparam xs (i+1))
			makeparam ((MT (DBoolL b) _):xs) i = 
				[param i $ toDataSource (C (if b then 1 else 0))] ++ (makeparam xs (i+1))
			-- Handle local variables
			-- makeparam ((MT (PDL (_,id)) _):xs) i = 
			-- 	[param i ()] ++ (makeparam xs (i+1))
			makeparam ys i = case ys of 
                                  (x:xs) -> (asmTransform x) ++ [param i (reg RAX)] ++ makeparam xs (i+1)
                                  [] -> []

			param i dtsrc = case i of
				0 -> (ld dtsrc RDI)
				1 -> (ld dtsrc RSI)
				2 -> (ld dtsrc RDX)
				3 -> (ld dtsrc RCX)
				4 -> (ld dtsrc R8)
				5 -> (ld dtsrc R9)
				otherwise -> (Push dtsrc)

asmAnd:: LowIRTree -> [AsmOp]
asmAnd = asmBinOp AndQ

asmOr:: LowIRTree -> [AsmOp]
asmOr = asmBinOp OrQ

asmAdd:: LowIRTree -> [AsmOp]
asmAdd = asmBinOp AddQ

asmSub:: LowIRTree -> [AsmOp]
asmSub = asmBinOp SubQ

asmMul:: LowIRTree -> [AsmOp]
asmMul = asmBinOp IMul

asmMod:: LowIRTree -> [AsmOp]
asmMod node@(MT stnode forest) = concat $ map asmTransform forest

asmDiv:: LowIRTree -> [AsmOp]
asmDiv node@(MT stnode forest) = concat $ map asmTransform forest

asmNot:: LowIRTree -> [AsmOp]
asmNot node@(MT stnode forest) = concat $ map asmTransform forest

asmNeg:: LowIRTree -> [AsmOp]
asmNeg node@(MT stnode forest) = concat $ map asmTransform forest

asmAssignPlus:: LowIRTree -> [AsmOp]
asmAssignPlus node@(MT stnode forest) = concat $ map asmTransform forest

asmAssignMinus:: LowIRTree -> [AsmOp]
asmAssignMinus node@(MT stnode forest) = concat $ map asmTransform forest

asmAssign:: LowIRTree -> [AsmOp]
asmAssign node@(MT stnode forest) = concat $ map asmTransform forest

asmNeql:: LowIRTree -> [AsmOp]
asmNeql node@(MT stnode forest) = concat $ map asmTransform forest

asmEql:: LowIRTree -> [AsmOp]
asmEql node@(MT stnode forest) = concat $ map asmTransform forest

asmLt:: LowIRTree -> [AsmOp]
asmLt node@(MT stnode forest) = concat $ map asmTransform forest

asmLte:: LowIRTree -> [AsmOp]
asmLte node@(MT stnode forest) = concat $ map asmTransform forest

asmGt:: LowIRTree -> [AsmOp]
asmGt node@(MT stnode forest) = concat $ map asmTransform forest

asmGte:: LowIRTree -> [AsmOp]
asmGte node@(MT stnode forest) = concat $ map asmTransform forest

asmLoc:: LowIRTree -> [AsmOp]
asmLoc node@(MT (LocL m) forest) = [ld m RAX]

asmDStr:: LowIRTree -> [AsmOp]
asmDStr node@(MT stnode forest) = concat $ map asmTransform forest

asmDChar:: LowIRTree -> [AsmOp]
asmDChar node@(MT (DCharL c) forest) = [ld (ord c) RAX]
asmDChar node@(MT _ forest) = []

asmDInt:: LowIRTree -> [AsmOp]
asmDInt node@(MT (DIntL i) forest) = [ld i RAX]
asmDInt node@(MT _ forest) = []


asmDBool:: LowIRTree -> [AsmOp]
asmDBool node@(MT stnode forest) = concat $ map asmTransform forest

asmDBlock:: LowIRTree -> [AsmOp]
asmDBlock node@(MT stnode forest) = concat $ map asmTransform forest

asmReturn:: LowIRTree -> [AsmOp]
asmReturn node@(MT stnode forest) = concat $ map asmTransform forest

asmBreak:: LowIRTree -> [AsmOp]
asmBreak node@(MT stnode forest) = concat $ map asmTransform forest

asmContinue:: LowIRTree -> [AsmOp]
asmContinue node@(MT stnode forest) = concat $ map asmTransform forest

asmIf:: LowIRTree -> [AsmOp]
asmIf node@(MT stnode forest) = concat $ map asmTransform forest

asmFor:: LowIRTree -> [AsmOp]
asmFor node@(MT stnode forest) = concat $ map asmTransform forest

asmWhile:: LowIRTree -> [AsmOp]
asmWhile node@(MT stnode forest) = concat $ map asmTransform forest

asmMD:: LowIRTree -> [AsmOp]
asmMD node@(MT (MDL (_,id)) forest) = [Lbl (idString id)] ++ (concat (map asmTransform forest )) ++ [Ret]

asmPD:: LowIRTree -> [AsmOp]
asmPD node@(MT _ forest) = concat $ map asmTransform forest

asmProg:: LowIRTree -> [AsmOp]
asmProg node@(MT _ forest) = concat $ (map asmTransform forest) ++ makeLabels dstrs
     where f (DStrL s) = [s]
           f _ = []
           getDStrs = concat . (map f)
           dstrs = getDStrs (listify node)
           g s = [Lbl $ '.' : getHashStr s, AsmString s]
           makeLabels = map g
