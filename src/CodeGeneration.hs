{-# LANGUAGE FlexibleInstances #-}


module CodeGeneration where

import Transforms
import Control.Monad
import Semantics
import Data.List
import Data.Char
import MultiTree
import Util
import RegisterAlloc

data DataSource = M MemLoc | C Int deriving (Eq) --memory location, or constant (immediate value)

data Register = RAX | RBX | RCX | RDX | RSP | RBP | RSI | RDI | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 deriving (Eq, Enum)
-- regs = map show $ [RBP, RSP] ++ [R12 .. R15]
regs = map show [RBX .. R15]

data MemLoc = Reg Register | EffectiveA Int MemLoc Register | BPOffset Int | Label String deriving (Eq)

instance ValidMemLoc Register where
    toMemLoc = Reg

class Registerizable a where
    reg :: Register -> a
    isReg :: a -> Bool
    getReg :: a -> Maybe Register

instance Registerizable Register where
    reg x = x
    isReg = const True
    getReg x = Just x 

instance Registerizable MemLoc where
    reg x = Reg x

    isReg (Reg _) = True
    isReg _ = False

    getReg (Reg x) = Just x
    getReg _ = Nothing

instance Show MemLoc where
	show (Reg r) = map toLower $ (show r)
	show (BPOffset i) = (show i)++"(%rbp)"
	show (Label str) = str
	show (EffectiveA i (Reg r1) r2) = show i ++ "(" ++ show r1 ++ ", " ++ show r2 ++ ", 8)"
    -- Temporary.. this is kind of shitty.. but we are going to move the label value into r11
	show (EffectiveA i (Label _) r) = show i ++ "(" ++ show R11 ++ ", " ++ show r ++ ", 8)"

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

class ValidMemLoc a where
    toMemLoc :: a -> MemLoc

instance ValidMemLoc MemLoc where
    toMemLoc = id

data AsmOp = Mov DataSource MemLoc
         | NegQ Register
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
         | Jle MemLoc
         | Jl MemLoc
         | Jge MemLoc
         | Jne MemLoc
         | AddQ DataSource MemLoc
         | AndQ DataSource MemLoc
         | OrQ DataSource MemLoc
         | XorQ DataSource MemLoc
         | SubQ DataSource MemLoc
      	 | Dec Register
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
	 | Data 
	 | Res Int
	 | Code String
         deriving (Eq)

instance Show DataSource where
	show (M ml) = show ml
	show (C i) = '$' : show i

instance Show AsmOp where
         show (NegQ r) = "neg " ++ show r
         show (Mov x@(M (EffectiveA _ (Label s) _)) y) = "mov $" ++ s ++ ", %r11\n" ++ "mov "++(show x)++", "++ (show y) 
         show (Mov x y@(EffectiveA _ (Label s) _)) = "mov $" ++ s ++ ", %r11\n" ++ "mov "++(show x)++", "++ (show y) 
         show (Mov x y) = "mov "++(show x)++", "++ (show y) 
         show (CMove x y) = "cmove "++(show x)++", "++ (show y) 
         show (CMovne x y) = "cmovne "++(show x)++", "++ (show y)
         show (CMovg x y) = "cmovg "++(show x)++", "++ (show y)
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
         show (Jle x) = "jle "++(show x)
         show (Jl x) = "jl "++(show x)
         show (Jge x) = "jge "++(show x)
         show (Jne x) = "jne "++(show x)
         show (AddQ x y) = "addq "++(show x)++", "++ (show y)
         show (AndQ x y) = "and "++(show x)++", "++ (show y)
         show (OrQ x y) = "or "++(show x)++", "++ (show y)
         show (XorQ x y) = "xor "++(show x)++", "++ (show y)
         show (SubQ x y) = "subq "++(show x)++", "++ (show y)
         show (Dec x) = "dec "++(show x)
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
         show Data = ".Data"
         show (Res n) = intercalate "\n" [".long 8"  | x <- [1..4*n] ] 
	 show (Code str) = str

----- Assembly generation helper functions

-- Takes a asmop constructor and makes it able to accept a broader range of inputs 
-- to help avoiding having to wrap constructors over and over
expandDomain :: (ValidDataSource a, ValidMemLoc b) => (DataSource -> MemLoc -> AsmOp) -> a -> b -> AsmOp
expandDomain op x y = op (toDataSource x) (toMemLoc y)

ld :: (ValidDataSource a, ValidMemLoc b) => a -> b -> AsmOp
ld = expandDomain Mov

push :: (ValidDataSource a) => a -> AsmOp
push x = Push (toDataSource x)

pop :: (ValidMemLoc a) => a -> AsmOp
pop x = Pop (toMemLoc x)

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


jumpif :: Bool -> String -> [AsmOp]
jumpif True s = [cmp (1 :: Int) RAX, Je (Label s)]
jumpif False s = [cmp (0 :: Int) RAX, Je (Label s)]

isGlobalAccess :: MemLoc -> Bool
isGlobalAccess (EffectiveA _ (Label _) _) = True
isGlobalAccess _ = False

-- Assumes value of index for array lookup is in RAX
checkArraySize :: Int -> [AsmOp]
checkArraySize n = [cmp (n :: Int) RAX]
                ++ [Jge (Label ".err_bound")]
                ++ [cmp (0 :: Int) RAX]
                ++ [Jl (Label ".err_bound")]

