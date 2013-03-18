module MemoryIRTree where

import MultiTree
import Semantics
import Transforms
import Data.Map as M hiding (map, foldl, filter, singleton)

type LowIRTree = MultiTree IRNode
data MemLoc = Reg Register | BPOffset Int | Label String deriving (Eq)

instance Show MemLoc where
	show (Reg r) = map toLower $ (show r)
	show (BPOffset i) = (show i)++"(%rbp)"
	show (Label str) = str

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
        
