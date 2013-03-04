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
type SemanticTree = MultiTree (pos, STNode)

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
            | FD FDType TypedId	-- Field declaration
            | CD Id		-- Callout declaration
            | PD TypedId	-- Parameter declaration
            | MD TypedId	-- Method declaration
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
    convert (P pos (Program cds fds mds)) =(pos, MT Prog children)
        where children = (map convert cds) ++ (concat . map getFieldDeclForest) fds ++ (map convert mds)

instance ConvertibleToST Block where 
    convert (P pos (Block fds stmts)) =(pos, MT DBlock $ (concat . map getFieldDeclForest) fds ++ map convert stmts)

instance ConvertibleToST ParamDecl where 
    convert (P pos (ParamDecl typ name)) =(pos, singleton $ PD (convertType typ, mkId name))

instance ConvertibleToST MethodDecl where 
    convert (P pos (MethodDecl typ name pds blk)) =(pos, MT (MD (convertType typ, mkId name)) $ map convert pds ++ [convert blk])

instance ConvertibleToST CalloutDecl where 
    convert (P pos (CalloutDecl name)) =(pos, singleton $ CD (mkId name))

instance ConvertibleToST Statement where 
    convert (P pos (AssignStatement loc op e)) =(pos, addChild (convert loc) $ addChild (convert e) $ convert op )
    convert (P pos (MethodCallStatement mc)) =(pos, convert mc)
    convert (P pos (IfStatement cond bl)) =(pos, MT If $ [convert cond, convert bl, convert (Block [] [])])
    convert (P pos (IfElseStatement cond t_block f_block)) =(pos, MT If $ [convert cond, convert t_block, convert f_block])
    convert (P pos (ForStatement idf e e' block)) =(pos, MT (For (mkId idf)) $ [convert e, convert e', convert block])
    convert (P pos (WhileStatement cond block)) =(pos, MT While $ [convert cond, convert block])
    convert (P pos (ReturnStatement e)) =(pos, MT Return $ [convert e])
    convert (P pos (EmptyReturnStatement)) =(pos, singleton Return)
    convert (P pos (BreakStatement)) =(pos, singleton Break)
    convert (P pos (ContinueStatement)) =(pos, singleton Continue)

instance ConvertibleToST AssignOp where 
    convert (P pos (AssignOp "=")) =(pos, singleton Assign)
    convert (P pos (AssignOp "+=")) =(pos, singleton AssignPlus)
    convert (P pos (AssignOp "-=")) =(pos, singleton AssignMinus)
    convert _ = undefined -- Redesign this perhaps because this kind of sucks

instance ConvertibleToST MethodCall where 
    convert (P pos (ParamlessMethodCall (MethodName s))) =(pos, singleton $ MethodCall (mkId s))
    convert (P pos (ExprParamMethodCall (MethodName s)) es) =(pos, MT (MethodCall (mkId s)) $ map convert es)
    convert (P pos (CalloutParamMethodCall (MethodName s)) cas) =(pos, MT (MethodCall (mkId s)) $ map convert cas)

instance ConvertibleToST CalloutArg where 
    convert (P pos (ExprCalloutArg e)) =(pos, convert e)
    convert (P pos (StringCalloutArg s)) =(pos, singleton (DStr s))

instance ConvertibleToST Location where 
    convert (P pos (Location s)) =(pos, singleton (Loc (mkId s)))
    convert (P pos (IndexedLocation s expr)) =(pos, MT (Loc (mkId s)) [convert expr])

instance ConvertibleToST Expr where 
    convert (P pos (OrExpr e e')) =(pos, MT Or $ [convert e, convert e'])
    convert (P pos (Expr1 e)) =(pos, convert e)

instance ConvertibleToST Expr1 where 
    convert (P pos (AndExpr e e')) =(pos, MT And $ [convert e, convert e'])
    convert (P pos (Expr2 e)) =(pos, convert e)

instance ConvertibleToST Expr2 where 
    convert (P pos (EqualExpr e e')) =(pos, MT Eql $ [convert e, convert e'])
    convert (P pos (NotEqualExpr e e')) =(pos, MT Neql $ [convert e, convert e'])
    convert (P pos (Expr3 e)) =(pos, convert e)

instance ConvertibleToST Expr3 where 
    convert (P pos (LTExpr e e')) =(pos, MT Lt $ [convert e, convert e'])
    convert (P pos (LTEExpr e e')) =(pos, MT Lte $ [convert e, convert e'])
    convert (P pos (GTExpr e e')) =(pos, MT Gt $ [convert e, convert e'])
    convert (P pos (GTEExpr e e')) =(pos, MT Gte $ [convert e, convert e'])
    convert (P pos (Expr4 e)) =(pos, convert e)

instance ConvertibleToST Expr4 where 
    convert (P pos (AddExpr e e')) =(pos, MT Add $ [convert e, convert e'])
    convert (P pos (SubtractExpr e e')) =(pos, MT Sub $ [convert e, convert e'])
    convert (P pos (Expr5 e)) =(pos, convert e)

instance ConvertibleToST Expr5 where 
    convert (P pos (MultiplyExpr e e')) =(pos, MT Mul $ [convert e, convert e'])
    convert (P pos (DivideExpr e e')) =(pos, MT Div $ [convert e, convert e'])
    convert (P pos (ModuloExpr e e')) =(pos, MT Mod $ [convert e, convert e'])
    convert (P pos (Expr6 e)) =(pos, convert e)

instance ConvertibleToST Expr6 where 
    convert (P pos (NegateExpr e)) =(pos, MT Neg $ map convert [e])
    convert (P pos (NotExpr e)) =(pos, MT Not $ map convert [e])
    convert (P pos (Expr7 e)) =(pos, convert e)

instance ConvertibleToST Expr7 where 
    convert (P pos (LiteralExpr lit)) =(pos, convert lit)
    convert (P pos (LocationExpr loc)) =(pos, convert loc)
    convert (P pos (MethodCallExpr mc)) =(pos, convert mc)
    convert (P pos (ParenExpr e)) =(pos, convert e)

instance ConvertibleToST Literal where 
    convert (P pos (Bool b)) =(pos, singleton (DBool b))
    convert (P pos (Int str)) =(pos, singleton (DInt (read str)) )
    convert (P pos (Char c)) =(pos, singleton (DChar c) )
