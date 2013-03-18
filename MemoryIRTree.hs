module MemoryIRTree where

import MultiTree
import Semantics
import Transforms

type LowIRTree = MultiTree IRNode

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
