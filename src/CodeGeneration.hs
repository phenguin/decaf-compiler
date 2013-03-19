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
	     | Pushall 
	     | Popall
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
         show (Enter x) = "enter $"++(show x) ++ ", $0"
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
         show (Pushall) = intercalate "\n" $ map ("push " ++) regs
         show (Popall)  = intercalate "\n" $ map ("pop " ++) (reverse regs)


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
            BreakL _                       ->asmBreak
            ContinueL _                    ->asmContinue
            IfL _ _                          ->asmIf
            ForL _ _ _                       ->asmFor
            WhileL _ _                       ->asmWhile
        --    FDL _ _                      ->asmFD
         --   CDL _                        ->asmCD
            PDL _                        ->asmPD
            MDL _                        ->asmMD
            ProgL                        ->asmProg
            _                           -> const []

asmTransform:: LowIRTree -> [AsmOp]
asmTransform node@(MT stnode _) = (handler stnode) node

-- Converts the final list of asmops into the correct output
getAssemblyStr :: SemanticTreeWithSymbols -> String
getAssemblyStr node = concat $ intersperse "\n" $ map show $ asmTransform $ convertToLowIRTree node

----- Assembly generation helper functions

-- Takes a asmop constructor and makes it able to accept a broader range of inputs 
-- to help avoiding having to wrap constructors over and over
expandDomain :: (ValidDataSource a, ValidMemLoc b) => (DataSource -> MemLoc -> AsmOp) -> a -> b -> AsmOp
expandDomain op x y = op (toDataSource x) (toMemLoc y)

ld :: (ValidDataSource a, ValidMemLoc b) => a -> b -> AsmOp
ld = expandDomain Mov

cmp :: (ValidDataSource a, ValidMemLoc b) => a -> b -> AsmOp
cmp = expandDomain Cmp

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

asmBinOpFlipArgs :: (Registerizable a, Registerizable b) => (a -> b -> AsmOp) -> LowIRTree -> [AsmOp]
asmBinOpFlipArgs binop node@(MT stnode (t1:t2:ts)) = asmTransform t2 ++ [ld RAX R10] ++ asmTransform t1 ++ [binop (reg R10) (reg RAX)]

jumpif :: Bool -> String -> [AsmOp]
jumpif True s = [cmp (1 :: Int) RAX, Je (Label s)]
jumpif False s = [cmp (0 :: Int) RAX, Je (Label s)]

asmMethodCall :: LowIRTree -> [AsmOp]
asmMethodCall node@(MT (MethodCallL id) forest) = 
    [Pushall]
	++ params 
	++ (if idString id == "printf" then [ld (0 :: Int) RAX] else []) 
	++ [Call (Label (idString id))] 
    ++ [Popall]
		where 	params =  makeparam forest 0
			makeparam ((MT (DStrL str) _):xs) i =  
				flipAfter5 i [param i $ toDataSource (Label ("$." ++ (getHashStr str))) ] (makeparam xs (i+1))
			makeparam ((MT (DCharL chrtr) _):xs) i = 
				flipAfter5 i [param i $ toDataSource (C (ord chrtr)) ] (makeparam xs (i+1))
			makeparam ((MT (DIntL intgr) _):xs) i = 
				flipAfter5 i [param i $ toDataSource (C intgr) ] (makeparam xs (i+1))
			makeparam ((MT (DBoolL b) _):xs) i = 
				flipAfter5 i [param i $ toDataSource (C (if b then 1 else 0))] (makeparam xs (i+1))
--			makeparam ((MT (PDL (_,str) _):xs) i = 
--			 	flipAfter5 i [param i (Mov (Label str) (reg RAX))] (makeparam xs (i+1)
			makeparam ys i = case ys of 
                                  (x:xs) -> (asmTransform x) ++ [param i (reg RAX)] ++ makeparam xs (i+1)
                                  [] -> []
			flipAfter5 i a b 
				|i > 5	=(b ++ a)
				| otherwise  =(a ++ b)
			param i dtsrc = case i of
				0 -> (ld dtsrc RDI)
				1 -> (ld dtsrc RSI)
				2 -> (ld dtsrc RDX)
				3 -> (ld dtsrc RCX)
				4 -> (ld dtsrc R8)
				5 -> (ld dtsrc R9)
				otherwise -> (Push dtsrc)

pass :: [LowIRTree] -> [AsmOp]
pass = concat . (map asmTransform)

asmAnd:: LowIRTree -> [AsmOp]
asmAnd = asmBinOp AndQ

asmOr:: LowIRTree -> [AsmOp]
asmOr = asmBinOp OrQ

asmAdd:: LowIRTree -> [AsmOp]
asmAdd = asmBinOp AddQ

asmSub:: LowIRTree -> [AsmOp]
asmSub = asmBinOpFlipArgs SubQ

asmMul:: LowIRTree -> [AsmOp]
asmMul = asmBinOp IMul

asmMod:: LowIRTree -> [AsmOp]
asmMod node@(MT stnode (t1:t2:ts)) = 
    (asmTransform t2)
    ++ [ld RAX R10]
    ++ asmTransform t1
    ++ [ld (0 :: Int) RDX]
    ++ [IDiv (toDataSource R10)]
    ++ [ld RDX RAX]

asmDiv:: LowIRTree -> [AsmOp]
asmDiv node@(MT stnode (t1:t2:ts)) = 
    (asmTransform t2)
    ++ [ld RAX R10]
    ++ asmTransform t1
    ++ [ld (0 :: Int) RDX]
    ++ [IDiv (toDataSource R10)]

asmNot:: LowIRTree -> [AsmOp]
asmNot node@(MT stnode forest) = pass forest

asmNeg:: LowIRTree -> [AsmOp]
asmNeg node@(MT stnode forest) = pass forest

asmAssignPlus:: LowIRTree -> [AsmOp]
asmAssignPlus node@(MT AssignPlusL ((MT (LocL ml) _):v:xs)) = 
					(asmTransform v) 
 					++ [(AddQ (reg RAX) ml)]

asmAssignMinus:: LowIRTree -> [AsmOp]
asmAssignMinus node@(MT AssignMinusL ((MT (LocL ml) _ ):v:xs)) = 
 					(asmTransform v) 
 					++ [(SubQ (reg RAX) ml )]

asmAssign:: LowIRTree -> [AsmOp]
asmAssign node@(MT AssignL ((MT (LocL ml) _):v:xs)) = 
 					(asmTransform v) 
 					++ [(Mov (reg RAX) ml )]

asmCompareOp :: (Register -> Register -> AsmOp) -> LowIRTree -> [AsmOp]
asmCompareOp op node@(MT stnode (x:y:xs)) = 	
 					(asmTransform x) 
 					++ [(ld RAX R10)] 
 					++ (asmTransform y) 
 					++ [cmp RAX R10] 
 					++ [(Mov (C 0) (reg RAX))] 
 					++ [(Mov (C 1) (reg R10))] 
 					++ [(op (reg R10) (reg RAX))]

asmNeql:: LowIRTree -> [AsmOp]
asmNeql = asmCompareOp CMovne

asmEql:: LowIRTree -> [AsmOp]
asmEql = asmCompareOp CMove

asmLt:: LowIRTree -> [AsmOp]
asmLt = asmCompareOp CMovl

asmLte:: LowIRTree -> [AsmOp]
asmLte = asmCompareOp CMovle

asmGt:: LowIRTree -> [AsmOp] 
asmGt = asmCompareOp CMovg

asmGte:: LowIRTree -> [AsmOp]
asmGte = asmCompareOp CMovge

-- Partially working.. implement arrays? need to change data types a bit?
asmLoc:: LowIRTree -> [AsmOp]
asmLoc node@(MT (LocL m) forest) = [ld m RAX]

asmDStr:: LowIRTree -> [AsmOp]
asmDStr node@(MT stnode forest) = pass forest

asmDChar:: LowIRTree -> [AsmOp]
asmDChar node@(MT (DCharL c) forest) = [ld (ord c) RAX]
asmDChar node@(MT _ forest) = []

asmDInt:: LowIRTree -> [AsmOp]
asmDInt node@(MT (DIntL i) forest) = [ld i RAX]
asmDInt node@(MT _ forest) = []

asmDBool:: LowIRTree -> [AsmOp]
asmDBool node@(MT (DBoolL b) forest) = [ld (C (if b then 1 else 0)) RAX]

asmDBlock:: LowIRTree -> [AsmOp]
asmDBlock node@(MT stnode forest) = pass forest

asmReturn:: LowIRTree -> [AsmOp]
asmReturn node@(MT ReturnL forest) = (concat $ map asmTransform forest) ++ [Leave, Ret]

asmBreak:: LowIRTree -> [AsmOp]
asmBreak node@(MT (BreakL str) _) = [Jmp (Label str)]

asmContinue:: LowIRTree -> [AsmOp]
asmContinue node@(MT (ContinueL str) _) = [Jmp (Label str)]

-- Working
asmIf:: LowIRTree -> [AsmOp]

-- If-else block
asmIf node@(MT (IfL elsel endl) (conde:thenb:elseb:xs)) = 
						asmTransform conde
                        ++ jumpif False elsel
						++ asmTransform thenb 
                        ++ [Jmp (Label endl)]
						++ [Lbl elsel]
						++ asmTransform elseb
                        ++ [Lbl endl]

-- If block without else
asmIf node@(MT (IfL _ endl) (conde:thenb:xs)) = 
						asmTransform conde
                        ++ jumpif False endl
						++ asmTransform thenb 
                        ++ [Lbl endl]

-- Not yet working I don't think -justin
asmFor:: LowIRTree -> [AsmOp]
asmFor node@(MT (ForL id startl endl) (starte:ende:body:xs)) =
						asmTransform starte
						++ [Mov (reg RAX) id]
						++ [Lbl startl]
						++ [AddQ (C 1) id]
						++ asmTransform ende
						++ [cmp RAX id]
						++ asmTransform body 
						++ [Jmp (Label startl)]
						++ [Lbl endl]
 

asmWhile:: LowIRTree -> [AsmOp]
asmWhile node@(MT (WhileL startl endl) (conde:body:xs)) = 
						[Lbl startl]
						++ asmTransform conde
						++ jumpif False endl
						++ asmTransform body
						++ [Jmp (Label startl)] 
						++ [Lbl endl]

countFieldDecs :: LowIRTree -> Int
countFieldDecs node@(MT _ forest) = length $ filter isFD $ concat $ map listify forest
    where isFD (FDL _ _) = True
          isFD _ = False


asmMD:: LowIRTree -> [AsmOp]
asmMD node@(MT (MDL (_,id)) forest) = [Lbl (idString id), Enter ((countFieldDecs node) * 8)] ++ (concat (map asmTransform forest )) ++ [Leave, Ret]

asmPD:: LowIRTree -> [AsmOp]
asmPD node@(MT _ forest) = pass forest

--- Store string constants in data section at the end of the program
asmProg:: LowIRTree -> [AsmOp]
asmProg node@(MT _ forest) = concat $ (map asmTransform forest) ++ makeLabels dstrs
     where f (DStrL s) = [s]
           f _ = []
           getDStrs = concat . (map f)
           dstrs = getDStrs (listify node)
           g s = [Lbl $ '.' : getHashStr s, AsmString s]
           makeLabels = map g
