
module CodeGeneration where

import Transforms

data Register = RAX | RBX | RCX | RDX | RSP | RBP | RSI | RDI | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 deriving (Show, Eq)

data MemLoc = Reg Register | BPOffset Int | Label String deriving (Show, Eq)
data DataSource = P Placeholder | M MemLoc | C Int deriving (Show, Eq) -- Placeholder, memory location, or constant (immediate value)
data Placeholder = ParamPH | LocalPH deriving (Eq, Show)


data AssmOp = Mov DataSource MemLoc
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
         | Add DataSource MemLoc
         | Sub DataSource MemLoc
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
            FD _ _                      ->asmFD
            CD _                        ->asmCD
            PD _                        ->asmPD
            MD _                        ->asmMD



asmTransform:: SemanticTreeWithSymbols -> AsmOp
asmTransform node@(MT (pos, stnode, st) _) = (handler stnode) node

asmMethodCall :: SemanticTreeWithSymbols -> [AsmOp]
asmMethodCall node@(MT (pos, (MethodCall id), st) forest) = 

asmAnd:: SemanticTreeWithSymbols -> [AsmOp]
asmAnd node@(MT (pos, stnode, st) forest) =

asmOr:: SemanticTreeWithSymbols -> [AsmOp]
asmOr node@(MT (pos, stnode, st) forest) =

asmAdd:: SemanticTreeWithSymbols -> [AsmOp]
asmAdd node@(MT (pos, stnode, st) forest) =

asmSub:: SemanticTreeWithSymbols -> [AsmOp]
asmSub node@(MT (pos, stnode, st) forest) =

asmMul:: SemanticTreeWithSymbols -> [AsmOp]
asmMul node@(MT (pos, stnode, st) forest) =

asmMod:: SemanticTreeWithSymbols -> [AsmOp]
asmMod node@(MT (pos, stnode, st) forest) =

asmDiv:: SemanticTreeWithSymbols -> [AsmOp]
asmDiv node@(MT (pos, stnode, st) forest) =

asmNot:: SemanticTreeWithSymbols -> [AsmOp]
asmNot node@(MT (pos, stnode, st) forest) =

asmNeg:: SemanticTreeWithSymbols -> [AsmOp]
asmNeg node@(MT (pos, stnode, st) forest) =

asmAssignPlus:: SemanticTreeWithSymbols -> [AsmOp]
asmAssignPlus node@(MT (pos, stnode, st) forest) =

asmAssignMinus:: SemanticTreeWithSymbols -> [AsmOp]
asmAssignMinus node@(MT (pos, stnode, st) forest) =

asmAssign:: SemanticTreeWithSymbols -> [AsmOp]
asmAssign node@(MT (pos, stnode, st) forest) =

asmNeql:: SemanticTreeWithSymbols -> [AsmOp]
asmNeql node@(MT (pos, stnode, st) forest) =

asmEql:: SemanticTreeWithSymbols -> [AsmOp]
asmEql node@(MT (pos, stnode, st) forest) =

asmLt:: SemanticTreeWithSymbols -> [AsmOp]
asmLt node@(MT (pos, stnode, st) forest) =

asmLte:: SemanticTreeWithSymbols -> [AsmOp]
asmLte node@(MT (pos, stnode, st) forest) =

asmGt:: SemanticTreeWithSymbols -> [AsmOp]
asmGt node@(MT (pos, stnode, st) forest) =

asmGte:: SemanticTreeWithSymbols -> [AsmOp]
asmGte node@(MT (pos, stnode, st) forest) =

asmLoc:: SemanticTreeWithSymbols -> [AsmOp]
asmLoc node@(MT (pos, stnode, st) forest) =

asmDStr:: SemanticTreeWithSymbols -> [AsmOp]
asmDStr node@(MT (pos, stnode, st) forest) =

asmDChar:: SemanticTreeWithSymbols -> [AsmOp]
asmDChar node@(MT (pos, stnode, st) forest) =

asmDInt:: SemanticTreeWithSymbols -> [AsmOp]
asmDInt node@(MT (pos, stnode, st) forest) =

asmDBool:: SemanticTreeWithSymbols -> [AsmOp]
asmDBool node@(MT (pos, stnode, st) forest) =

asmDBlock:: SemanticTreeWithSymbols -> [AsmOp]
asmDBlock node@(MT (pos, stnode, st) forest) =

asmReturn:: SemanticTreeWithSymbols -> [AsmOp]
asmReturn node@(MT (pos, stnode, st) forest) =

asmBreak:: SemanticTreeWithSymbols -> [AsmOp]
asmBreak node@(MT (pos, stnode, st) forest) =

asmContinue:: SemanticTreeWithSymbols -> [AsmOp]
asmContinue node@(MT (pos, stnode, st) forest) =

asmIf:: SemanticTreeWithSymbols -> [AsmOp]
asmIf node@(MT (pos, stnode, st) forest) =

asmFor:: SemanticTreeWithSymbols -> [AsmOp]
asmFor node@(MT (pos, stnode, st) forest) =

asmWhile:: SemeanticTreeWithSymbols -> [AsmOp]
asmWhile node@(MT (pos, stnode, st) forest) =

