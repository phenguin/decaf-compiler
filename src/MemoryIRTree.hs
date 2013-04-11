module MemoryIRTree where

import MultiTree
import Data.Char (toLower)
import Semantics
import Transforms
import Data.Map as M hiding (map, foldl, filter, singleton)
import Data.IORef
import System.IO.Unsafe
import RegisterAlloc

type LowIRTree = MultiTree IRNode
type VarBindings = M.Map String MemLoc


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
            | LocL Int MemLoc -- Int is the size for array locations for RT checks
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
convertToLowIRTree = (convertToLowIRTree' Nothing Nothing) . numberTree . (fmap (\(_,node,st) -> (node, st)))

convertToLowIRTree' :: Maybe (String, String) -> Maybe VarBindings -> MultiTree ((STNode, SymbolTable), Int) -> LowIRTree
convertToLowIRTree' lbls _ node@(MT ((Prog, _), _) forest) = (MT ProgL (map (convertToLowIRTree' lbls (Just table)) forest))
    where table = getVarBindings node

convertToLowIRTree' lbls bs (MT (((MethodCall x), _), _) forest) = (MT (MethodCallL x) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((And, _), n) forest) = (MT (AndL n) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Or, _), n) forest) = (MT (OrL n) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Add, _), _) forest) = (MT AddL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Sub, _), _) forest) = (MT SubL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Mul, _), _) forest) = (MT MulL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Mod, _), _) forest) = (MT ModL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Div, _), _) forest) = (MT DivL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Not, _), _) forest) = (MT NotL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Neg, _), _) forest) = (MT NegL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((AssignPlus, _), _) forest) = (MT AssignPlusL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((AssignMinus, _), _) forest) = (MT AssignMinusL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Assign, _), _) forest) = (MT AssignL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Neql, _), _) forest) = (MT NeqlL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Eql, _), _) forest) = (MT EqlL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Lt, _), _) forest) = (MT LtL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Lte, _), _) forest) = (MT LteL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Gt, _), _) forest) = (MT GtL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Gte, _), _) forest) = (MT GteL (map (convertToLowIRTree' lbls bs) forest))

convertToLowIRTree' lbls Nothing (MT (((Loc i), _), _) forest) = error "unexpected Location access outside of method body"

convertToLowIRTree' lbls (Just table) (MT (((Loc i), symbolTable), _) forest@(x:xs)) = 
    (MT (LocL arrSize ml) (map (convertToLowIRTree' lbls (Just table)) forest))
    where ml = f (table ! (idString i))
          arrSize = g $ lookupSymbol i symbolTable
          g Nothing = error "Uncaught semantic error: Undefined symbol"
          g (Just x) = case x of
              (FDesc (Array size) _) -> size
              _ -> error "Uncaught semantic error: Got wrong descriptor"
          f (BPOffset off) = EffectiveA off (toMemLoc RBP) RAX
          f ml@(Label str) = EffectiveA 0 ml RAX
          f ml@(EffectiveA _ _ _) = ml
          f _ = error "Cannot have array valued parameters"

convertToLowIRTree' lbls (Just table) (MT (((Loc i), _), _) forest) = 
    (MT (LocL (-1) (table ! (idString i))) (map (convertToLowIRTree' lbls (Just table)) forest))

convertToLowIRTree' lbls bs (MT (((DStr s), _), _) forest) = (MT (DStrL s) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (((DChar c), _), _) forest) = (MT (DCharL c) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (((DInt n), _), _) forest) = (MT (DIntL n) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (((DBool b), _), _) forest) = (MT (DBoolL b) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((DBlock, _), _) forest) = (MT DBlockL (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT ((Return, _), _) forest) = (MT ReturnL (map (convertToLowIRTree' lbls bs) forest))

convertToLowIRTree' Nothing bs (MT ((Break, _), _) forest) = error "No label passed to break statement"
convertToLowIRTree' lbls@(Just (_, s2)) bs (MT ((Break, _), _) forest) = (MT (BreakL s2) (map (convertToLowIRTree' lbls bs) forest))

convertToLowIRTree' Nothing bs (MT ((Continue, _), _) forest) = error "No label passed to continue statement"
convertToLowIRTree' lbls@(Just (s1, _)) bs (MT ((Continue, _), _) forest) = (MT (ContinueL s1) (map (convertToLowIRTree' lbls bs) forest))

convertToLowIRTree' lbls bs (MT ((If, _), num) forest) = 
                                   (MT (IfL s1 s2) (map (convertToLowIRTree' lbls bs) forest))
    where s = show num
          s1 = ".ifend" ++ s
          s2 = ".elseend" ++ s

convertToLowIRTree' lbls Nothing (MT (((For i), _), _) forest) = error "No variable bindings passed for for statement"

convertToLowIRTree' lbls bs@(Just table) (MT (((For i), _), num) forest) = 
    (MT (ForL (table ! idString i) s1 s2) (map (convertToLowIRTree' (Just (s1, s2)) bs) forest))
    where s = show num
          s1 = ".forstart" ++ s
          s2 = ".forend" ++ s

convertToLowIRTree' lbls bs (MT ((While, _), num) forest) = 
    (MT (WhileL s1 s2) (map (convertToLowIRTree' (Just (s1, s2)) bs) forest))
    where s = show num
          s1 = ".whilestart" ++ s
          s2 = ".whileend" ++ s

convertToLowIRTree' lbls bs (MT (((FD ftp ti), _), _) forest) = (MT (FDL ftp ti) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (((CD i), _), _) forest) = (MT (CDL i) (map (convertToLowIRTree' lbls bs) forest))
convertToLowIRTree' lbls bs (MT (((PD ti), _), _) forest) = (MT (PDL ti) (map (convertToLowIRTree' lbls bs) forest))

convertToLowIRTree' lbls bs node@(MT (((MD ti), _), _) forest) = (MT (MDL ti) (map (convertToLowIRTree' lbls (Just combinedTable)) forest))
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
getVarBindings = getVarBindings' . fmap (fst . fst)

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
        
