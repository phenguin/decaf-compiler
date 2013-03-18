{-# LANGUAGE FlexibleInstances #-}

module CodeGeneration where

import Transforms
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

data Register = RAX | RBX | RCX | RDX | RSP | RBP | RSI | RDI | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 deriving (Eq)

instance Show Register where
    show RAX = "%rax"
    show RBX = "%rbx"
    show RCX = "%rcx"
    show RDX = "%rdx"
    show RSP = "%rsp"
    show RBP = "%rbp"
    show RSI = "%rsi"
    show RDI = "%rdi"
    show R8 = "%r8"
    show R9 = "%r9"
    show R10 = "%r10"
    show R11 = "%r11"
    show R12 = "%r12"
    show R13 = "%r13"
    show R14 = "%r14"
    show R15 = "%r15"

data MemLoc = Reg Register | BPOffset Int | Label String deriving (Eq)
data DataSource = M MemLoc | C Int deriving (Eq) -- Placeholder, memory location, or constant (immediate value)
data MaybePlaceholder a = PH String | Val a deriving (Eq)

instance (Show a) => Show (MaybePlaceholder a) where
    show (PH s) = s ++ ":_"
    show (Val x) = show x

instance Monad MaybePlaceholder where
    return = Val
    (PH s) >>= _ = PH s
    (Val x) >>= f = f x

instance Functor MaybePlaceholder where
    fmap = liftM

data AsmOp = Mov (MaybePlaceholder DataSource) (MaybePlaceholder MemLoc)
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

instance Show MemLoc where
	show (Reg r) = map toLower $ (show r)
	show (BPOffset i) = (show i)++"(%rbp)"
	show (Label str) = str

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

handler:: STNode -> (SemanticTreeWithSymbols -> [AsmOp])
handler node = case node of
            MethodCall _                ->asmMethodCall
            And                         ->asmAnd
            Or                          ->asmOr
            Add                         ->asmAdd
            Sub                         ->asmSub
            Mul                         ->asmMul
            Mod                         ->asmMod
            Div                         ->asmDiv
            Not                         ->asmNot
            Neg                         ->asmNeg
            AssignPlus                  ->asmAssignPlus
            AssignMinus                 ->asmAssignMinus
            Assign                      ->asmAssign
            Neql                        ->asmNeql
            Eql                         ->asmEql
            Lt                          ->asmLt
            Lte                         ->asmLte
            Gt                          ->asmGt
            Gte                         ->asmGte
            Loc _                       ->asmLoc
            DStr _                      ->asmDStr
            DChar _                     ->asmDChar
            DInt _                      ->asmDInt
            DBool _                     ->asmDBool
            DBlock                      ->asmDBlock
            Return                      ->asmReturn
            Break                       ->asmBreak
            Continue                    ->asmContinue
            If                          ->asmIf
            For _                       ->asmFor
            While                       ->asmWhile
        --    FD _ _                      ->asmFD
         --   CD _                        ->asmCD
            PD _                        ->asmPD
            MD _                        ->asmMD
            Prog                        ->asmProg
            _                           -> const []

asmTransform:: SemanticTreeWithSymbols -> [AsmOp]
asmTransform node@(MT (pos, stnode, st) _) = (handler stnode) node

getAssemblyStr :: SemanticTreeWithSymbols -> String
getAssemblyStr node = concat $ intersperse "\n" $ map show $ asmTransform node

----- Assembly generation helper functions
ld :: (ValidDataSource a, ValidMemLoc b) => a -> b -> AsmOp
ld x y = Mov (return $ toDataSource x) (return $ toMemLoc y)

class ValidMemLoc a where
    toMemLoc :: a -> MemLoc

instance ValidMemLoc MemLoc where
    toMemLoc = id

instance ValidMemLoc Register where
    toMemLoc = Reg

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

class Registerizable a where
    reg :: Register -> a
    isReg :: a -> Bool
    getReg :: a -> Maybe Register

instance (Registerizable a) => Registerizable (MaybePlaceholder a) where
    reg = return . reg

instance Registerizable Register where
    reg x = x
    isReg = const True
    getReg x = Just x 

instance Registerizable DataSource where
    reg x = M (reg x)

    isReg (M (Reg _)) = True
    isReg _ = False

    getReg (M (Reg x)) = Just x
    getReg _ = Nothing

instance Registerizable MemLoc where
    reg x = Reg x

    isReg (Reg _) = True
    isReg _ = False

    getReg (Reg x) = Just x
    getReg _ = Nothing

asmBinOp :: (Registerizable a, Registerizable b) => (a -> b -> AsmOp) -> SemanticTreeWithSymbols -> [AsmOp]
asmBinOp binop node@(MT (pos, stnode, st) (t1:t2:ts)) = asmTransform t1 ++ [ld RAX R10] ++ asmTransform t2 ++ [binop (reg R10) (reg RAX)]

asmMethodCall :: SemanticTreeWithSymbols -> [AsmOp]
asmMethodCall node@(MT (pos, (MethodCall id), st) forest) =  
	 params ++ (if idString id == "printf" then [ld (0 :: Int) RAX] else []) ++ [Call (Label (idString id))]
		where 	params =  makeparam forest 0
			makeparam ((MT (pos,(DStr str),st) _):xs) i =  
				[param i $ toDataSource (Label ("$." ++ (getHashStr str))) ] ++ (makeparam xs (i+1))
			makeparam ((MT (_,(DChar chrtr),_) _):xs) i = 
				[param i $ toDataSource (C (ord chrtr)) ] ++ (makeparam xs (i+1))
			makeparam ((MT (_,(DInt intgr),_) _):xs) i = 
				[param i $ toDataSource (C intgr) ] ++ (makeparam xs (i+1))
			makeparam ((MT (_,(DBool b),_) _):xs) i = 
				[param i $ toDataSource (C (if b then 1 else 0))] ++ (makeparam xs (i+1))
			-- Handle local variables
			-- makeparam ((MT (_,(PD (_,id)),_) _):xs) i = 
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

asmAnd:: SemanticTreeWithSymbols -> [AsmOp]
asmAnd = asmBinOp AndQ

asmOr:: SemanticTreeWithSymbols -> [AsmOp]
asmOr = asmBinOp OrQ

asmAdd:: SemanticTreeWithSymbols -> [AsmOp]
asmAdd = asmBinOp AddQ

asmSub:: SemanticTreeWithSymbols -> [AsmOp]
asmSub = asmBinOp SubQ

asmMul:: SemanticTreeWithSymbols -> [AsmOp]
asmMul = asmBinOp IMul

asmMod:: SemanticTreeWithSymbols -> [AsmOp]
asmMod node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmDiv:: SemanticTreeWithSymbols -> [AsmOp]
asmDiv node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmNot:: SemanticTreeWithSymbols -> [AsmOp]
asmNot node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmNeg:: SemanticTreeWithSymbols -> [AsmOp]
asmNeg node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmAssignPlus:: SemanticTreeWithSymbols -> [AsmOp]
asmAssignPlus node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmAssignMinus:: SemanticTreeWithSymbols -> [AsmOp]
asmAssignMinus node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmAssign:: SemanticTreeWithSymbols -> [AsmOp]
asmAssign node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmNeql:: SemanticTreeWithSymbols -> [AsmOp]
asmNeql node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmEql:: SemanticTreeWithSymbols -> [AsmOp]
asmEql node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmLt:: SemanticTreeWithSymbols -> [AsmOp]
asmLt node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmLte:: SemanticTreeWithSymbols -> [AsmOp]
asmLte node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmGt:: SemanticTreeWithSymbols -> [AsmOp]
asmGt node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmGte:: SemanticTreeWithSymbols -> [AsmOp]
asmGte node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmLoc:: SemanticTreeWithSymbols -> [AsmOp]
asmLoc node@(MT (pos, (Loc i), st) forest) = [Mov (PH $ idString i) (reg RAX)]

asmDStr:: SemanticTreeWithSymbols -> [AsmOp]
asmDStr node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmDChar:: SemanticTreeWithSymbols -> [AsmOp]
asmDChar node@(MT (pos, (DChar c), st) forest) = [ld (ord c) RAX]
asmDChar node@(MT (pos, _, st) forest) = []

asmDInt:: SemanticTreeWithSymbols -> [AsmOp]
asmDInt node@(MT (pos, (DInt i), st) forest) = [ld i RAX]
asmDInt node@(MT (pos, _, st) forest) = []


asmDBool:: SemanticTreeWithSymbols -> [AsmOp]
asmDBool node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmDBlock:: SemanticTreeWithSymbols -> [AsmOp]
asmDBlock node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmReturn:: SemanticTreeWithSymbols -> [AsmOp]
asmReturn node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmBreak:: SemanticTreeWithSymbols -> [AsmOp]
asmBreak node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmContinue:: SemanticTreeWithSymbols -> [AsmOp]
asmContinue node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmIf:: SemanticTreeWithSymbols -> [AsmOp]
asmIf node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmFor:: SemanticTreeWithSymbols -> [AsmOp]
asmFor node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmWhile:: SemanticTreeWithSymbols -> [AsmOp]
asmWhile node@(MT (pos, stnode, st) forest) = concat $ map asmTransform forest

asmMD:: SemanticTreeWithSymbols -> [AsmOp]
asmMD node@(MT (pos, (MD (_,id)), st) forest) = [Lbl (idString id)] ++ (concat (map asmTransform forest )) ++ [Ret]

asmPD:: SemanticTreeWithSymbols -> [AsmOp]
asmPD node@(MT (pos, _, st) forest) = concat $ map asmTransform forest

asmProg:: SemanticTreeWithSymbols -> [AsmOp]
asmProg node@(MT (pos, _ , st) forest) = concat $ (map asmTransform forest) ++ makeLabels dstrs
     where f (_, DStr s, _) = [s]
           f _ = []
           getDStrs = concat . (map f)
           dstrs = getDStrs (listify node)
           g s = [Lbl $ '.' : getHashStr s, AsmString s]
           makeLabels = map g
