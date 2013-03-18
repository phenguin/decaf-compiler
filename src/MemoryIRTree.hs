module MemoryIRTree where

import MultiTree
import Data.Char (toLower)
import Semantics
import Transforms
import Data.Map as M hiding (map, foldl, filter, singleton)

type LowIRTree = MultiTree IRNode
type VarBindings = M.Map String MemLoc

data Register = RAX | RBX | RCX | RDX | RSP | RBP | RSI | RDI | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 deriving (Eq)

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

data MemLoc = Reg Register | BPOffset Int | Label String deriving (Eq)

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

data IRNode = ProgL
            | MethodCallL Id
            | AndL
            | OrL
            | AddL
            | SubL
            | MulL
            | ModL
            | DivL
            | NotL
            | NegL
            | AssignPlusL
            | AssignMinusL
            | AssignL
            | NeqlL
            | EqlL
            | LtL
            | LteL
            | GtL
            | GteL
            | LocL Id
            | DStrL String
            | DCharL Char
            | DIntL Int
            | DBoolL Bool
            | DBlockL
            | ReturnL
            | BreakL
            | ContinueL
            | IfL
            | ForL Id
            | WhileL
            | FDL FDType TypedId
            | CDL Id
            | PDL TypedId
            | MDL TypedId
     deriving (Show, Eq)

convertToLowIRTree :: MultiTree STNode -> LowIRTree
convertToLowIRTree = undefined

-- Should only be called on a MD node.. will not play well when called at a higher level
-- bindings for parameters in order
-- parameters negative rbp offset, locals positive
paramBindings :: [MemLoc]
paramBindings = map reg [RDI, RSI, RDX, RCX, R8, R9] ++ map (BPOffset . (*(-8))) [1..]
getVarBindings :: SemanticTreeWithSymbols -> VarBindings
getVarBindings = getVarBindings' . fmap second
    where second (_, x, _) = x

getVarBindings' :: MultiTree STNode -> VarBindings
getVarBindings' node = third $ foldl f (1, paramBindings, M.empty) $ listify node
    where f (n, (x:xs), bs) (PD (_, i)) = (n, xs, M.insert (idString i) x bs)
          f (n, xs, bs) (FD _ (_, i)) = (n+1, xs, M.insert (idString i) (BPOffset (8*n)) bs)
          f acc _ = acc
          third (_,_,x) = x

testMethod :: MultiTree STNode
testMethod = MT (MD (IntType, mkId "fact")) chillens 
chillens = [ singleton (PD (IntType, mkId "n")),
    MT DBlock [ 
        singleton (FD Single (BoolType, mkId "b")),
        singleton (FD Single (IntType, mkId "a")) 
        ]
        ]
        
