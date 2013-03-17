{-# LANGUAGE FlexibleInstances #-}
module Transforms where

import Parser 
import MultiTree
import Data.Hashable (hash)

data LitType = IntType | BoolType | VoidType | StrType deriving (Show, Eq)
data FDType = Single | Array Int deriving (Show, Eq, Ord)

data Id = IdWithHash {hashInt::Int , idString::String} deriving (Ord)

mkId :: String -> Id
mkId s = IdWithHash (hash s) s

instance Eq Id where
    (IdWithHash h1 s1) == (IdWithHash h2 s2) = (h1 == h2) && (s1 == s2)

instance Show Id where
    show (IdWithHash _ name) = name

type TypedId = (LitType, Id)
type SemanticTree = MultiTree (Pos, STNode)

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
     deriving (Show, Eq)

class ConvertibleToST a where
    convert :: a -> SemanticTree

convertType :: Type -> LitType
convertType (Type "int") = IntType
convertType (Type "boolean") = BoolType
convertType (Type "void") = VoidType
convertType _ = undefined -- Also redesign this perhaps.. fuck strings

getFieldDeclForest :: WithPos FieldDecl -> [SemanticTree]
getFieldDeclForest (P pos (FieldDecl typ cds)) = map f cds
    where f (P pos (VarDecl name)) = singleton $ (pos, FD Single ((convertType . getVal) typ, (mkId . getVal) name))
          f (P pos (ArrayDecl name size)) = singleton $ (pos, FD (Array (read $ getVal size)) ((convertType . getVal) typ, (mkId . getVal) name))

fromRight :: Either a b -> b
fromRight (Right b) = b

--------------------------------

instance ConvertibleToST Program where 
    convert (Program cds fds mds) = MT ((1,1), Prog) children
        where children = (map convert cds) ++ (concat . map getFieldDeclForest) fds ++ (map convert mds)

instance ConvertibleToST (WithPos Block) where 
    convert (P pos (Block fds stmts)) = MT (pos, DBlock) $ (concat . map getFieldDeclForest ) fds ++ map convert stmts

instance ConvertibleToST (WithPos ParamDecl) where 
    convert (P pos (ParamDecl typ name)) = singleton $ (pos, PD ((convertType . getVal) typ, (mkId . getVal) name))

instance ConvertibleToST (WithPos MethodDecl) where 
    convert (P pos (MethodDecl typ name pds blk)) = MT (pos, (MD ((convertType . getVal) typ, (mkId . getVal) name))) $ map convert pds ++ [convert blk]

instance ConvertibleToST (WithPos CalloutDecl) where 
    convert (P pos (CalloutDecl name)) = singleton $ (pos, CD ((mkId . getVal) name))

instance ConvertibleToST (WithPos Statement) where 
    convert (P pos (AssignStatement loc op e)) = addChild (convert loc) $ addChild (convert e) $ convert op 
    convert (P pos (MethodCallStatement mc)) = convert mc
    convert (P pos (IfStatement cond bl)) = MT (pos, If) $ [convert cond, convert bl]
    convert (P pos (IfElseStatement cond t_block f_block)) = MT (pos, If) $ [convert cond, convert t_block, convert f_block]
    convert (P pos (ForStatement idf e e' block)) = MT (pos, (For ((mkId . getVal) idf))) $ [convert e, convert e', convert block]
    convert (P pos (WhileStatement cond block)) = MT (pos, While) $ [convert cond, convert block]
    convert (P pos (ReturnStatement e)) = MT (pos, Return) $ [convert e]
    convert (P pos (EmptyReturnStatement)) = singleton (pos, Return)
    convert (P pos (BreakStatement)) = singleton (pos, Break)
    convert (P pos (ContinueStatement)) = singleton (pos, Continue)

instance ConvertibleToST (WithPos AssignOp) where 
    convert (P pos (AssignOp "=")) = singleton (pos, Assign)
    convert (P pos (AssignOp "+=")) = singleton (pos, AssignPlus)
    convert (P pos (AssignOp "-=")) = singleton (pos, AssignMinus)
    convert _ = undefined -- Redesign this perhaps because this kind of sucks

instance ConvertibleToST (WithPos MethodCall) where 
    convert (P pos (ParamlessMethodCall (P pos2 (MethodName s)))) = singleton $ (pos, MethodCall $ (mkId . getVal) s)
    convert (P pos (ExprParamMethodCall (P pos2 (MethodName s)) es)) = MT (pos, (MethodCall $ (mkId . getVal) s)) $ map convert es
    convert (P pos (CalloutParamMethodCall (P pos2 (MethodName s)) cas)) = MT (pos, (MethodCall $ (mkId . getVal) s)) $ map convert cas

instance ConvertibleToST (WithPos CalloutArg) where 
    convert (P pos (ExprCalloutArg e)) = convert e
    convert (P pos (StringCalloutArg s)) = singleton (pos, (DStr s))

instance ConvertibleToST (WithPos Location) where 
    convert (P pos (Location s)) = singleton (pos, (Loc ((mkId . getVal) s)))
    convert (P pos (IndexedLocation s expr)) = MT (pos, (Loc ((mkId . getVal) s))) [convert expr]

instance ConvertibleToST (WithPos Expr) where 
    convert (P pos (OrExpr e e')) = MT (pos, Or) $ [convert e, convert e']
    convert (P pos (Expr1 e)) = convert e

instance ConvertibleToST (WithPos Expr1) where 
    convert (P pos (AndExpr e e')) = MT (pos, And) $ [convert e, convert e']
    convert (P pos (Expr2 e)) = convert e

instance ConvertibleToST (WithPos Expr2) where 
    convert (P pos (EqualExpr e e')) = MT (pos, Eql) $ [convert e, convert e']
    convert (P pos (NotEqualExpr e e')) = MT (pos, Neql) $ [convert e, convert e']
    convert (P pos (Expr3 e)) = convert e

instance ConvertibleToST (WithPos Expr3) where 
    convert (P pos (LTExpr e e')) = MT (pos, Lt) $ [convert e, convert e']
    convert (P pos (LTEExpr e e')) = MT (pos, Lte) $ [convert e, convert e']
    convert (P pos (GTExpr e e')) = MT (pos, Gt) $ [convert e, convert e']
    convert (P pos (GTEExpr e e')) = MT (pos, Gte) $ [convert e, convert e']
    convert (P pos (Expr4 e)) = convert e

instance ConvertibleToST (WithPos Expr4) where 
    convert (P pos (AddExpr e e')) = MT (pos, Add) $ [convert e, convert e']
    convert (P pos (SubtractExpr e e')) = MT (pos, Sub) $ [convert e, convert e']
    convert (P pos (Expr5 e)) = convert e

instance ConvertibleToST (WithPos Expr5) where 
    convert (P pos (MultiplyExpr e e')) = MT (pos, Mul) $ [convert e, convert e']
    convert (P pos (DivideExpr e e')) = MT (pos, Div) $ [convert e, convert e']
    convert (P pos (ModuloExpr e e')) = MT (pos, Mod) $ [convert e, convert e']
    convert (P pos (Expr6 e)) = convert e

instance ConvertibleToST (WithPos Expr6) where 
    convert (P pos (NegateExpr (P _ (LiteralExpr (P _ (Int str)))))) = singleton (pos, DInt $ -1 * (read str))
    convert (P pos (NegateExpr e)) = MT (pos, Neg) $ map convert [e]
-- no instance of these negateexpr' and notexpr', safe to delete?
 --   convert (P pos (NegateExpr' e)) = MT (pos, Neg) $ map convert [e]
    convert (P pos (NotExpr e)) = MT (pos, Not) $ map convert [e]
 --   convert (P pos (NotExpr' e)) = MT (pos, Not) $ map convert [e]
    convert (P pos (Expr7 e)) = convert e

instance ConvertibleToST (WithPos Expr7) where 
    convert (P pos (LiteralExpr lit)) = convert lit
    convert (P pos (LocationExpr loc)) = convert loc
    convert (P pos (MethodCallExpr mc)) = convert mc
    convert (P pos (ParenExpr e)) = convert e

instance ConvertibleToST (WithPos Literal) where 
    convert (P pos (Bool b)) = singleton (pos, (DBool b))
    convert (P pos (Int str)) = singleton (pos, (DInt (read str)))
    convert (P pos (Char c)) = singleton (pos, (DChar c))
