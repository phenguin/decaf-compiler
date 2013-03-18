
module CodeGeneration where

import Transforms
import MultiTree
import Semantics
import Data.List

data Register = RAX | RBX | RCX | RDX | RSP | RBP | RSI | RDI | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 deriving (Show, Eq)

data MemLoc = Reg Register | BPOffset Int | Label String deriving (Show, Eq)
data DataSource = M MemLoc | C Int deriving (Show, Eq) -- Placeholder, memory location, or constant (immediate value)
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
<<<<<<< HEAD
         | Lbl String
	 deriving (Eq, Show)



=======
         deriving (Eq)

instance Show AsmOp where
         show (CMove x y) = "" 
         show (CMovne x y) = ""
         show (CMovg x y) = ""
         show (CMovl x y) = ""
         show (CMovge x y) = ""
         show (CMovle x y) = ""
         show (Enter x) = ""
         show Leave = "leave"
         show (Push x) = ""
         show (Pop x) = ""
         show (Call x) = ""
         show Ret = "ret"
         show (Jmp x) = ""
         show (Je x) = ""
         show (Jne x) = ""
         show (AddQ x y) = ""
         show (AndQ x y) = ""
         show (OrQ x y) = ""
         show (XorQ x y) = ""
         show (SubQ x y) = ""
         show (IMul x y) = ""
         show (IDiv x) = ""
         show (Shr x) = ""
         show (Shl x) = ""
         show (Ror x y) = ""
         show (Cmp x y) = ""
>>>>>>> Start working on show code for assmops

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
asmMod node@(MT (pos, stnode, st) forest) = undefined

asmDiv:: SemanticTreeWithSymbols -> [AsmOp]
asmDiv node@(MT (pos, stnode, st) forest) = undefined

asmNot:: SemanticTreeWithSymbols -> [AsmOp]
asmNot node@(MT (pos, stnode, st) forest) = undefined

asmNeg:: SemanticTreeWithSymbols -> [AsmOp]
asmNeg node@(MT (pos, stnode, st) forest) = undefined

asmAssignPlus:: SemanticTreeWithSymbols -> [AsmOp]
asmAssignPlus node@(MT (pos, stnode, st) forest) = undefined

asmAssignMinus:: SemanticTreeWithSymbols -> [AsmOp]
asmAssignMinus node@(MT (pos, stnode, st) forest) = undefined

asmAssign:: SemanticTreeWithSymbols -> [AsmOp]
asmAssign node@(MT (pos, stnode, st) forest) = undefined

asmNeql:: SemanticTreeWithSymbols -> [AsmOp]
asmNeql node@(MT (pos, stnode, st) forest) = undefined

asmEql:: SemanticTreeWithSymbols -> [AsmOp]
asmEql node@(MT (pos, stnode, st) forest) = undefined

asmLt:: SemanticTreeWithSymbols -> [AsmOp]
asmLt node@(MT (pos, stnode, st) forest) = undefined

asmLte:: SemanticTreeWithSymbols -> [AsmOp]
asmLte node@(MT (pos, stnode, st) forest) = undefined

asmGt:: SemanticTreeWithSymbols -> [AsmOp]
asmGt node@(MT (pos, stnode, st) forest) = undefined

asmGte:: SemanticTreeWithSymbols -> [AsmOp]
asmGte node@(MT (pos, stnode, st) forest) = undefined

asmLoc:: SemanticTreeWithSymbols -> [AsmOp]
asmLoc node@(MT (pos, stnode, st) forest) = undefined

asmDStr:: SemanticTreeWithSymbols -> [AsmOp]
asmDStr node@(MT (pos, stnode, st) forest) = undefined

asmDChar:: SemanticTreeWithSymbols -> [AsmOp]
asmDChar node@(MT (pos, (DChar char) , st) forest) = undefined

asmDInt:: SemanticTreeWithSymbols -> [AsmOp]
asmDInt node@(MT (pos, stnode, st) forest) = undefined

asmDBool:: SemanticTreeWithSymbols -> [AsmOp]
asmDBool node@(MT (pos, stnode, st) forest) = undefined

asmDBlock:: SemanticTreeWithSymbols -> [AsmOp]
asmDBlock node@(MT (pos, stnode, st) forest) = undefined

asmReturn:: SemanticTreeWithSymbols -> [AsmOp]
asmReturn node@(MT (pos, stnode, st) forest) = undefined

asmBreak:: SemanticTreeWithSymbols -> [AsmOp]
asmBreak node@(MT (pos, stnode, st) forest) = undefined

asmContinue:: SemanticTreeWithSymbols -> [AsmOp]
asmContinue node@(MT (pos, stnode, st) forest) = undefined

asmIf:: SemanticTreeWithSymbols -> [AsmOp]
asmIf node@(MT (pos, stnode, st) forest) = undefined

asmFor:: SemanticTreeWithSymbols -> [AsmOp]
asmFor node@(MT (pos, stnode, st) forest) = undefined

asmWhile:: SemanticTreeWithSymbols -> [AsmOp]
asmWhile node@(MT (pos, stnode, st) forest) = undefined

asmMD:: SemanticTreeWithSymbols -> [AsmOp]
asmMD node@(MT (pos, (MD (_,id)), st) forest) = [Lbl (idString id)] ++ (concat (map asmTransform forest ))

asmPD:: SemanticTreeWithSymbols -> [AsmOp]
asmPD node@(MT (pos, (MD (_,id)), st) forest) = []

asmProg:: SemanticTreeWithSymbols -> [AsmOp]
asmProg node@(MT (pos, _ , st) forest) = concat $ map asmTransform forest
