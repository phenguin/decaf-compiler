
module CodeGeneration where

import Transforms
import MultiTree
import Semantics

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
         | SubQ DataSource MemLoc
         | IMul DataSource MemLoc
         | IDiv DataSource
         | Shr Register
         | Shl Register
         | Ror DataSource MemLoc
         | Cmp DataSource MemLoc
         deriving (Eq, Show)




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
            -- FD _ _                      ->asmFD
            -- CD _                        ->asmCD
            -- PD _                        ->asmPD
            -- MD _                        ->asmMD



asmTransform:: SemanticTreeWithSymbols -> [AsmOp]
asmTransform node@(MT (pos, stnode, st) _) = (handler stnode) node

asmMethodCall :: SemanticTreeWithSymbols -> [AsmOp]
asmMethodCall node@(MT (pos, (MethodCall id), st) forest) = undefined

asmAnd:: SemanticTreeWithSymbols -> [AsmOp]
asmAnd node@(MT (pos, stnode, st) forest) = undefined

asmOr:: SemanticTreeWithSymbols -> [AsmOp]
asmOr node@(MT (pos, stnode, st) forest) = undefined

asmAdd:: SemanticTreeWithSymbols -> [AsmOp]
asmAdd node@(MT (pos, stnode, st) forest) = undefined

asmSub:: SemanticTreeWithSymbols -> [AsmOp]
asmSub node@(MT (pos, stnode, st) forest) = undefined

asmMul:: SemanticTreeWithSymbols -> [AsmOp]
asmMul node@(MT (pos, stnode, st) forest) = undefined

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
asmDChar node@(MT (pos, stnode, st) forest) = undefined

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

