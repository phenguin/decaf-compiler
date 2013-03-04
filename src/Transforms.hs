module Transforms where

import Main (parse, testParse)
import Parser 
import MultiTree
import Data.Hashable (hash)

data LitType = IntType | BoolType | VoidType deriving (Show)
data FDType = Single | Array Int deriving (Show)

data Id = IdWithHash Int String deriving (Ord)

mkId :: String -> Id
mkId s = IdWithHash (hash s) s

instance Eq Id where
    (IdWithHash h1 s1) == (IdWithHash h2 s2) = (h1 == h2) && (s1 == s2)

instance Show Id where
    show (IdWithHash _ name) = name



type TypedId = (LitType, Id)
type SemanticTree = MultiTree STNode

data STNode = Prog
            | MethodCall Id
            | And
            | Or
            | Add
            | Sub
            | Mul
            | Mod
            | Div
            | Not
            | Neg
            | AssignPlus
            | AssignMinus
            | Assign
            | Neql
            | Eql
            | Lt
            | Lte
            | Gt
            | Gte
            | Loc Id
            | DStr String
            | DChar Char
            | DInt Int
            | DBool Bool
            | DBlock
            | Return
            | Break
            | Continue
            | If
            | For Id
            | While
            | FD FDType TypedId
            | CD Id
            | PD TypedId
            | MD TypedId
     deriving (Show)

class ConvertibleToST a where
    convert :: a -> SemanticTree

convertType :: Type -> LitType
convertType (Type "int") = IntType
convertType (Type "boolean") = BoolType
convertType (Type "void") = VoidType
convertType _ = undefined -- Also redesign this perhaps.. fuck strings

getFieldDeclForest :: FieldDecl -> [SemanticTree]
getFieldDeclForest (FieldDecl typ cds) = map f cds
    where f (VarDecl name) = singleton $ FD Single (convertType typ, mkId name)
          f (ArrayDecl name size) = singleton $ FD (Array (read size)) (convertType typ, mkId name)

prettyIRTree :: (SemanticTree -> String) -> FilePath -> String
prettyIRTree f fp = case testParse fp of
    Left err -> err
    Right program -> f $ convert program

putIRTree :: FilePath -> IO ()
putIRTree = putStrLn . prettyIRTree pPrint

fromRight :: Either a b -> b
fromRight (Right b) = b

putIRTreeTabbed :: FilePath -> IO ()
putIRTreeTabbed = putStrLn . prettyIRTree pPrintTabbed

--------------------------------

instance ConvertibleToST Program where 
    convert (Program cds fds mds) = MT Prog children
        where children = (map convert cds) ++ (concat . map getFieldDeclForest) fds ++ (map convert mds)

instance ConvertibleToST Block where 
    convert (Block fds stmts) = MT DBlock $ (concat . map getFieldDeclForest) fds ++ map convert stmts

instance ConvertibleToST ParamDecl where 
    convert (ParamDecl typ name) = singleton $ PD (convertType typ, mkId name)

instance ConvertibleToST MethodDecl where 
    convert (MethodDecl typ name pds blk) = MT (MD (convertType typ, mkId name)) $ map convert pds ++ [convert blk]

instance ConvertibleToST CalloutDecl where 
    convert (CalloutDecl name) = singleton $ CD (mkId name)

instance ConvertibleToST Statement where 
    convert (AssignStatement loc op e) = addChild (convert loc) $ addChild (convert e) $ convert op 
    convert (MethodCallStatement mc) = convert mc
    convert (IfStatement cond bl) = MT If $ [convert cond, convert bl, convert (Block [] [])]
    convert (IfElseStatement cond t_block f_block) = MT If $ [convert cond, convert t_block, convert f_block]
    convert (ForStatement idf e e' block) = MT (For (mkId idf)) $ [convert e, convert e', convert block]
    convert (WhileStatement cond block) = MT While $ [convert cond, convert block]
    convert (ReturnStatement e) = MT Return $ [convert e]
    convert (EmptyReturnStatement) = singleton Return
    convert (BreakStatement) = singleton Break
    convert (ContinueStatement) = singleton Continue

instance ConvertibleToST AssignOp where 
    convert (AssignOp "=") = singleton Assign
    convert (AssignOp "+=") = singleton AssignPlus
    convert (AssignOp "-=") = singleton AssignMinus
    convert _ = undefined -- Redesign this perhaps because this kind of sucks

instance ConvertibleToST MethodCall where 
    convert (ParamlessMethodCall (MethodName s)) = singleton $ MethodCall (mkId s)
    convert (ExprParamMethodCall (MethodName s) es) = MT (MethodCall (mkId s)) $ map convert es
    convert (CalloutParamMethodCall (MethodName s) cas) = MT (MethodCall (mkId s)) $ map convert cas

instance ConvertibleToST CalloutArg where 
    convert (ExprCalloutArg e) = convert e
    convert (StringCalloutArg s) = singleton (DStr s)

instance ConvertibleToST Location where 
    convert (Location s) = singleton (Loc (mkId s))
    convert (IndexedLocation s expr) = MT (Loc (mkId s)) [convert expr]

instance ConvertibleToST Expr where 
    convert (OrExpr e e') = MT Or $ [convert e, convert e']
    convert (Expr1 e) = convert e

instance ConvertibleToST Expr1 where 
    convert (AndExpr e e') = MT And $ [convert e, convert e']
    convert (Expr2 e) = convert e

instance ConvertibleToST Expr2 where 
    convert (EqualExpr e e') = MT Eql $ [convert e, convert e']
    convert (NotEqualExpr e e') = MT Neql $ [convert e, convert e']
    convert (Expr3 e) = convert e

instance ConvertibleToST Expr3 where 
    convert (LTExpr e e') = MT Lt $ [convert e, convert e']
    convert (LTEExpr e e') = MT Lte $ [convert e, convert e']
    convert (GTExpr e e') = MT Gt $ [convert e, convert e']
    convert (GTEExpr e e') = MT Gte $ [convert e, convert e']
    convert (Expr4 e) = convert e

instance ConvertibleToST Expr4 where 
    convert (AddExpr e e') = MT Add $ [convert e, convert e']
    convert (SubtractExpr e e') = MT Sub $ [convert e, convert e']
    convert (Expr5 e) = convert e

instance ConvertibleToST Expr5 where 
    convert (MultiplyExpr e e') = MT Mul $ [convert e, convert e']
    convert (DivideExpr e e') = MT Div $ [convert e, convert e']
    convert (ModuloExpr e e') = MT Mod $ [convert e, convert e']
    convert (Expr6 e) = convert e

instance ConvertibleToST Expr6 where 
    convert (NegateExpr e) = MT Neg $ map convert [e]
    convert (NotExpr e) = MT Not $ map convert [e]
    convert (Expr7 e) = convert e

instance ConvertibleToST Expr7 where 
    convert (LiteralExpr lit) = convert lit
    convert (LocationExpr loc) = convert loc
    convert (MethodCallExpr mc) = convert mc
    convert (ParenExpr e) = convert e

instance ConvertibleToST Literal where 
    convert (Bool b) = singleton (DBool b)
    convert (Int str) = singleton (DInt (read str)) 
    convert (Char c) = singleton (DChar c) 
