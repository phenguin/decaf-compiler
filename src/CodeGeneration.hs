
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
