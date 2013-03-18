
module CodeGeneration where

import Transforms
import MultiTree
import Semantics
import Data.List
import Data.Char

data Register = RAX | RBX | RCX | RDX | RSP | RBP | RSI | RDI | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 deriving (Show, Eq)

data MemLoc = Reg Register | BPOffset Int | Label String deriving (Eq)
data DataSource = M MemLoc | C Int deriving (Eq) -- Placeholder, memory location, or constant (immediate value)
data Placeholder a = ParamPH | LocalPH deriving (Eq, Show)

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
         deriving (Eq)

instance Show DataSource where
	show (M ml) = show ml
	show (C i) = show i

instance Show MemLoc where
	show (Reg r) = map toLower (show r)
	show (BPOffset i) = (show i)++"(%rbp)"
	show (Label str) = str

instance Show AsmOp where
         show (CMove x y) = "mov "++(show x)++" , "++ (show y) 
         show (CMovne x y) = "cmove"++(show x)++" , "++ (show y)
         show (CMovg x y) = "cmovne"++(show x)++" , "++ (show y)
         show (CMovl x y) = "cmovl"++(show x)++" , "++ (show y)
         show (CMovge x y) = "cmovge"++(show x)++" , "++ (show y)
         show (CMovle x y) = "cmovle"++(show x)++" , "++ (show y)
         show (Enter x) = "enter"++(show x)
         show Leave = "leave"
         show (Push x) = "push"++(show x)
         show (Pop x) = "pop"++(show x)
         show (Call x) = "call"++(show x)
         show Ret = "ret"
         show (Jmp x) = "jmp"++(show x)
         show (Je x) = "je"++(show x)
         show (Jne x) = "jne"++(show x)
         show (AddQ x y) = "addq"++(show x)++" , "++ (show y)
         show (AndQ x y) = "and"++(show x)++" , "++ (show y)
         show (OrQ x y) = "or"++(show x)++" , "++ (show y)
         show (XorQ x y) = "xor"++(show x)++" , "++ (show y)
         show (SubQ x y) = "subq"++(show x)++" , "++ (show y)
         show (IMul x y) = "imul"++(show x)++" , "++ (show y)
         show (IDiv x) = "idiv"++(show x)
         show (Shr x) = "shr"++(show x)
         show (Shl x) = "shl"++(show x)
         show (Ror x y) = "ror"++(show x)++" , "++ (show y)
         show (Cmp x y) = "cmp"++(show x)++" , "++ (show y)

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

class Registerizable a where
    reg :: Register -> a
    isReg :: a -> Bool
    getReg :: a -> Maybe Register

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
asmBinOp binop node@(MT (pos, stnode, st) (t1:t2:ts)) = asmTransform t1 ++ [Mov (reg RAX) (reg R10)] ++ asmTransform t2 ++ [binop (reg R10) (reg RAX)]

asmTransform:: SemanticTreeWithSymbols -> [AsmOp]
asmTransform node@(MT (pos, stnode, st) _) = (handler stnode) node

asmMethodCall :: SemanticTreeWithSymbols -> [AsmOp]
asmMethodCall node@(MT (pos, (MethodCall id), st) forest) =  intercalate [Push (reg RAX)] (map asmTransform forest) ++ [Call (Label (idString id))]

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
asmMod node@(MT (pos, stnode, st) forest) = []

asmDiv:: SemanticTreeWithSymbols -> [AsmOp]
asmDiv node@(MT (pos, stnode, st) forest) = []

asmNot:: SemanticTreeWithSymbols -> [AsmOp]
asmNot node@(MT (pos, stnode, st) forest) = []

asmNeg:: SemanticTreeWithSymbols -> [AsmOp]
asmNeg node@(MT (pos, stnode, st) forest) = []

asmAssignPlus:: SemanticTreeWithSymbols -> [AsmOp]
asmAssignPlus node@(MT (pos, stnode, st) forest) = []

asmAssignMinus:: SemanticTreeWithSymbols -> [AsmOp]
asmAssignMinus node@(MT (pos, stnode, st) forest) = []

asmAssign:: SemanticTreeWithSymbols -> [AsmOp]
asmAssign node@(MT (pos, stnode, st) forest) = []

asmNeql:: SemanticTreeWithSymbols -> [AsmOp]
asmNeql node@(MT (pos, stnode, st) forest) = []

asmEql:: SemanticTreeWithSymbols -> [AsmOp]
asmEql node@(MT (pos, stnode, st) forest) = []

asmLt:: SemanticTreeWithSymbols -> [AsmOp]
asmLt node@(MT (pos, stnode, st) forest) = []

asmLte:: SemanticTreeWithSymbols -> [AsmOp]
asmLte node@(MT (pos, stnode, st) forest) = []

asmGt:: SemanticTreeWithSymbols -> [AsmOp]
asmGt node@(MT (pos, stnode, st) forest) = []

asmGte:: SemanticTreeWithSymbols -> [AsmOp]
asmGte node@(MT (pos, stnode, st) forest) = []

asmLoc:: SemanticTreeWithSymbols -> [AsmOp]
asmLoc node@(MT (pos, stnode, st) forest) = []

asmDStr:: SemanticTreeWithSymbols -> [AsmOp]
asmDStr node@(MT (pos, stnode, st) forest) = []

asmDChar:: SemanticTreeWithSymbols -> [AsmOp]
asmDChar node@(MT (pos, (DChar char) , st) forest) = []

asmDInt:: SemanticTreeWithSymbols -> [AsmOp]
asmDInt node@(MT (pos, stnode, st) forest) = []

asmDBool:: SemanticTreeWithSymbols -> [AsmOp]
asmDBool node@(MT (pos, stnode, st) forest) = []

asmDBlock:: SemanticTreeWithSymbols -> [AsmOp]
asmDBlock node@(MT (pos, stnode, st) forest) = []

asmReturn:: SemanticTreeWithSymbols -> [AsmOp]
asmReturn node@(MT (pos, stnode, st) forest) = []

asmBreak:: SemanticTreeWithSymbols -> [AsmOp]
asmBreak node@(MT (pos, stnode, st) forest) = []

asmContinue:: SemanticTreeWithSymbols -> [AsmOp]
asmContinue node@(MT (pos, stnode, st) forest) = []

asmIf:: SemanticTreeWithSymbols -> [AsmOp]
asmIf node@(MT (pos, stnode, st) forest) = []

asmFor:: SemanticTreeWithSymbols -> [AsmOp]
asmFor node@(MT (pos, stnode, st) forest) = []

asmWhile:: SemanticTreeWithSymbols -> [AsmOp]
asmWhile node@(MT (pos, stnode, st) forest) = []

asmMD:: SemanticTreeWithSymbols -> [AsmOp]
asmMD node@(MT (pos, (MD (_,id)), st) forest) = [Lbl (idString id)] ++ (concat (map asmTransform forest ))

asmPD:: SemanticTreeWithSymbols -> [AsmOp]
asmPD node@(MT (pos, (MD (_,id)), st) forest) = []

asmProg:: SemanticTreeWithSymbols -> [AsmOp]
asmProg node@(MT (pos, _ , st) forest) = concat $ map asmTransform forest
