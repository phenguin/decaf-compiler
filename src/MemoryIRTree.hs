module MemoryIRTree where

import MultiTree
import Data.Char (toLower)
import Semantics
import Transforms
import Data.Map as M hiding (map, foldl, filter, singleton)
import Data.IORef
import System.IO.Unsafe

type LowIRTree = MultiTree IRNode
type VarBindings = M.Map String MemLoc

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

data IRNode = ProgL
            | MethodCallL Id
            | AndL Int
            | OrL Int
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
            | LocL MemLoc
            | DStrL String
            | DCharL Char
            | DIntL Int
            | DBoolL Bool
            | DBlockL
            | ReturnL
            | BreakL String
            | ContinueL String
            | IfL String String
            | ForL MemLoc String String
            | WhileL String String
            | FDL FDType TypedId
            | CDL Id
            | PDL TypedId
            | MDL TypedId
     deriving (Show, Eq)

convertToLowIRTree :: SemanticTreeWithSymbols -> LowIRTree
convertToLowIRTree = (convertToLowIRTree' Nothing Nothing) . numberTree . (fmap (\(_,x,_) -> x))

convertToLowIRTree' :: Maybe (String, String) -> Maybe VarBindings -> MultiTree (STNode, Int) -> LowIRTree
convertToLowIRTree' lbls _ node@(MT (Prog, _) forest) = (MT ProgL (map (convertToLowIRTree' lbls (Just table)) forest))
    where table = getVarBindings node

convertToLowIRTree' lbls bs (MT ((MethodCall x), _) forest) = (MT (MethodCallL x) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (And, n) forest) = (MT (AndL n) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Or, n) forest) = (MT (OrL n) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Add, _) forest) = (MT AddL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Sub, _) forest) = (MT SubL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Mul, _) forest) = (MT MulL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Mod, _) forest) = (MT ModL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Div, _) forest) = (MT DivL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Not, _) forest) = (MT NotL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Neg, _) forest) = (MT NegL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (AssignPlus, _) forest) = (MT AssignPlusL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (AssignMinus, _) forest) = (MT AssignMinusL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Assign, _) forest) = (MT AssignL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Neql, _) forest) = (MT NeqlL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Eql, _) forest) = (MT EqlL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Lt, _) forest) = (MT LtL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Lte, _) forest) = (MT LteL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Gt, _) forest) = (MT GtL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Gte, _) forest) = (MT GteL (map (convertToLowIRTree' lbls bs) forest))

convertToLowIRTree' lbls Nothing (MT ((Loc i), _) forest) = error "unexpected Location access outside of method body"

convertToLowIRTree' lbls (Just table) (MT ((Loc i), _) forest@(x:xs)) = 
    (MT (LocL ml) (map (convertToLowIRTree' lbls (Just table)) forest))
    where ml = f (table ! (idString i))
          f (BPOffset off) = EffectiveA off (toMemLoc RBP) RAX
          f ml@(Label str) = EffectiveA 0 ml RAX
          f ml@(EffectiveA _ _ _) = ml
          f _ = error "Cannot have array valued parameters"

convertToLowIRTree' lbls (Just table) (MT ((Loc i), _) forest) = 
    (MT (LocL (table ! (idString i))) (map (convertToLowIRTree' lbls (Just table)) forest))

convertToLowIRTree' lbls bs (MT ((DStr s), _) forest) = (MT (DStrL s) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((DChar c), _) forest) = (MT (DCharL c) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((DInt n), _) forest) = (MT (DIntL n) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((DBool b), _) forest) = (MT (DBoolL b) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (DBlock, _) forest) = (MT DBlockL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (Return, _) forest) = (MT ReturnL (map (convertToLowIRTree' lbls bs) forest))

convertToLowIRTree' Nothing bs (MT (Break, _) forest) = error "No label passed to break statement"
convertToLowIRTree' lbls@(Just (_, s2)) bs (MT (Break, _) forest) = (MT (BreakL s2) (map (convertToLowIRTree' lbls bs) forest))

convertToLowIRTree' Nothing bs (MT (Continue, _) forest) = error "No label passed to continue statement"
convertToLowIRTree' lbls@(Just (s1, _)) bs (MT (Continue, _) forest) = (MT (ContinueL s1) (map (convertToLowIRTree' lbls bs) forest))

convertToLowIRTree' lbls bs (MT (If, num) forest) = 
                                   (MT (IfL s1 s2) (map (convertToLowIRTree' lbls bs) forest))
    where s = show num
          s1 = ".ifend" ++ s
          s2 = ".elseend" ++ s

convertToLowIRTree' lbls Nothing (MT ((For i), _) forest) = error "No variable bindings passed for for statement"

convertToLowIRTree' lbls bs@(Just table) (MT ((For i), num) forest) = 
    (MT (ForL (table ! idString i) s1 s2) (map (convertToLowIRTree' (Just (s1, s2)) bs) forest))
    where s = show num
          s1 = ".forstart" ++ s
          s2 = ".forend" ++ s

convertToLowIRTree' lbls bs (MT (While, num) forest) = 
    (MT (WhileL s1 s2) (map (convertToLowIRTree' (Just (s1, s2)) bs) forest))
    where s = show num
          s1 = ".whilestart" ++ s
          s2 = ".whileend" ++ s

convertToLowIRTree' lbls bs (MT ((FD ftp ti), _) forest) = (MT (FDL ftp ti) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((CD i), _) forest) = (MT (CDL i) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((PD ti), _) forest) = (MT (PDL ti) (map (convertToLowIRTree' lbls bs) forest))

convertToLowIRTree' lbls bs node@(MT ((MD ti), _) forest) = (MT (MDL ti) (map (convertToLowIRTree' lbls (Just combinedTable)) forest))
    where table = getVarBindings node
          combinedTable = case bs of
              Nothing -> table
              (Just bindings) -> M.union table bindings  -- Combine with global bindings.. shadowing where neccessary

convertToLowIRTree' _ _ _ = error "Unexpected node type in convertToLowIRTree"

-- Should only be called on a MD node.. will not play well when called at a higher level
-- bindings for parameters in order
-- parameters negative rbp offset, locals positive
paramBindings :: [MemLoc]
paramBindings = map reg [RDI, RSI, RDX, RCX, R8, R9] ++ map (BPOffset . (\x-> (x*8)+8)) [1..]
getVarBindings :: MultiTree (STNode, Int) -> VarBindings
getVarBindings = getVarBindings' . fmap fst

getVarBindings' :: MultiTree STNode -> VarBindings
getVarBindings' (MT Prog forest) = foldl f (M.empty) $ map nodeName forest
    where f bs (FD Single (_, i)) = M.insert (idString i) (Label $ ".global_" ++ idString i) bs
          f bs (FD (Array _) (_, i)) = M.insert (idString i) (EffectiveA 0 (Label $ ".global_" ++ idString i) RAX) bs
          f bs _ = bs

getVarBindings' node = third $ foldl f (1, paramBindings, M.empty) $ listify node
    where f (n, (x:xs), bs) (PD (_, i)) = (n, xs, M.insert (idString i) x bs)
          f (n, xs, bs) (FD _ (_, i)) = (n+1, xs, M.insert (idString i) (BPOffset (-8*n)) bs)
          f acc _ = acc
          third (_,_,x) = x

testMethod :: MultiTree STNode
testMethod = MT (MD (IntType, mkId "fact")) chillens 
chillens = [ singleton (PD (IntType, mkId "n")),
    MT DBlock [ 
        singleton (FD Single (BoolType, mkId "b")),
        singleton (FD Single (IntType, mkId "a")),
        singleton (Loc $ mkId "a"),
        singleton (Loc $ mkId "n"),
        singleton (Loc $ mkId "b")
        ]
        ]
        
