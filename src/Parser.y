-- Parser -- Decaf parser                                       -*- haskell -*-
-- Copyright (C) 2013  Benjamin Barenblat <bbaren@mit.edu>
--
-- This file is a part of decafc.
--
-- decafc is free software: you can redistribute it and/or modify it under the
-- terms of the MIT (X11) License as described in the LICENSE file.
--
-- decafc is distributed in the hope that it will be useful, but WITHOUT ANY
-- WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
-- FOR A PARTICULAR PURPOSE.  See the X11 license for more details.
{
module Parser where

import Text.Printf (printf)

import Scanner (ScannedToken(..), Token(..))

}


--------------------------------- Directives ----------------------------------

%name parse
%error { parseError }
%monad { Either String }

%tokentype { ScannedToken }

%token
  id { ScannedToken _ _ (Identifier _) }
  "{"        { ScannedToken _ _ LCurly }
  "}"        { ScannedToken _ _ RCurly }
  "("        { ScannedToken _ _ LParen }
  ")"        { ScannedToken _ _ RParen }
  "["        { ScannedToken _ _ LSquare }
  "]"        { ScannedToken _ _ RSquare }
  ";"        { ScannedToken _ _ SemiColon }
  "!"        { ScannedToken _ _ Not }
  ","        { ScannedToken _ _ Comma }

  bool { ScannedToken _ _ (BoolLiteral _) }
  string { ScannedToken _ _ (StringLiteral _) }
  char { ScannedToken _ _ (CharLiteral _) }
  int { ScannedToken _ _ (Number _) }

  "-"        { ScannedToken _ _ (Symbol "-") }

  "+" { ScannedToken _ _ (Symbol "+") }
  "*" { ScannedToken _ _ (Symbol "*") }
  "/" { ScannedToken _ _ (Symbol "/") }
  "%" { ScannedToken _ _ (Symbol "%") }

  "<" { ScannedToken _ _ (Symbol "<") }
  "<=" { ScannedToken _ _ (Symbol "<=") }
  ">=" { ScannedToken _ _ (Symbol ">=") }
  ">" { ScannedToken _ _ (Symbol ">") }

  "==" { ScannedToken _ _ (Symbol "==") }
  "!=" { ScannedToken _ _ (Symbol "!=") }

  "=" { ScannedToken _ _ (Symbol "=") }
  "+=" { ScannedToken _ _ (Symbol "+=") }
  "-=" { ScannedToken _ _ (Symbol "-=") }

  "&&" { ScannedToken _ _ (Symbol "&&") }
  "||" { ScannedToken _ _ (Symbol "||") }

  data_type { ScannedToken _ _ (DataType _) }
  if { ScannedToken _ _ If }
  for { ScannedToken _ _ For }
  while { ScannedToken _ _ While }
  return { ScannedToken _ _ Return }
  break { ScannedToken _ _ Break }
  continue { ScannedToken _ _ Continue }
  else { ScannedToken _ _ Else }
  void { ScannedToken _ _ Void }
  callout { ScannedToken _ _ Callout }

%% -------------------------------- Grammar -----------------------------------

Program : CalloutDecls FieldDecls MethodDecls { Program $1 $2 $3}

MethodDecls : {- empty -} { [] }
            | MethodDecl MethodDecls { $1 : $2 }

MethodDecl : Type id "(" ")" Block { propogatePos $1 $ MethodDecl $1 (extractPosString $2) [] $5 }
           | Type id "(" ParamDecls ")" Block { propogatePos $1 $ MethodDecl $1 (extractPosString $2) $4 $6 }
           | void id "(" ")" Block { propogatePos $1 $ MethodDecl (propogatePos $1 (Type "void")) (extractPosString $2) [] $5 }
           | void id "(" ParamDecls ")" Block { propogatePos $1 $ MethodDecl (propogatePos $1 (Type "void")) (extractPosString $2) $4 $6 }

Type : data_type { propogatePos $1 $ extractType $1 }

FieldDecl : Type CommaDecls ";" { propogatePos $1 $ FieldDecl $1 $2 }

FieldDecls : {- empty -} { [] }
           | FieldDecls FieldDecl { $2 : $1 }

CalloutDecl : callout id ";" { propogatePos $1 $ CalloutDecl (extractPosString $2) }

CalloutDecls : {- empty -} { [] }
             | CalloutDecl CalloutDecls { $1 : $2 }

Block : "{" FieldDecls Statements "}" { propogatePos $1 $ Block $2 $3 }
      | "{" Statements "}" { propogatePos $1 $ Block [] $2 }

ParamDecl : Type id { propogatePos $1 $ ParamDecl $1 (extractPosString $2) }

ParamDecls : ParamDecl { [$1] }
           | ParamDecl "," { [$1] }
           | ParamDecl "," ParamDecls { $1 : $3 }

Statement : Location AssignOp Expr ";" { propogatePos $1 $ AssignStatement $1 $2 $3 }
        | MethodCall ";" { propogatePos $1 $ MethodCallStatement $1 }
        | if "(" Expr ")" Block { propogatePos $1 $ IfStatement $3 $5 }
        | if "(" Expr ")" Block else Block { propogatePos $1 $ IfElseStatement $3 $5 $7 }
        | for "(" id "=" Expr ";" Expr ")" Block { propogatePos $1 $ ForStatement (extractPosString $3) $5 $7 $9 }
        | while "(" Expr ")" Block { propogatePos $1 $ WhileStatement $3 $5 }
        | return Expr ";" { propogatePos $1 $ ReturnStatement $2 }
        | return ";" { propogatePos $1 $ EmptyReturnStatement }
        | break ";" { propogatePos $1 $ BreakStatement }
        | continue ";" { propogatePos $1 $ ContinueStatement }

Statements : {- empty -} { [] }
           | Statement Statements { $1 : $2 }

AssignOp : "=" { propogatePos $1 $ AssignOp "=" }
        | "+=" { propogatePos $1 $ AssignOp "+=" }
        | "-=" { propogatePos $1 $ AssignOp "-=" }

MethodCall : MethodName "(" ")" { propogatePos $1 $ ParamlessMethodCall $1 }
        | MethodName "(" CommaExprs ")" { propogatePos $1 $ ExprParamMethodCall $1 $3 }
        | MethodName "(" CommaCalloutArgs ")" { propogatePos $1 $ CalloutParamMethodCall $1 $3 }

MethodName : id { propogatePos $1 $ MethodName (extractPosString $1) }

Location : id { propogatePos $1 $ Location (extractPosString $1) }
        | id "[" Expr "]" { propogatePos $1 $ IndexedLocation (extractPosString $1) $3 }

-- Order of operations stuff
Expr : Expr "||" Expr1 { propogatePos $1 $ OrExpr $1 $3 }
     | Expr1 { propogatePos $1 $ Expr1 $1 }

Expr1 : Expr1 "&&" Expr2 { propogatePos $1 $ AndExpr $1 $3 }
     | Expr2 { propogatePos $1 $ Expr2 $1 }

Expr2 : Expr2 "==" Expr3 { propogatePos $1 $ EqualExpr $1 $3 }
     | Expr2 "!=" Expr3 { propogatePos $1 $ NotEqualExpr $1 $3 } 
     | Expr3 { propogatePos $1 $ Expr3 $1 }

Expr3 : Expr3 "<" Expr4 { propogatePos $1 $ LTExpr $1 $3 }
     | Expr3 "<=" Expr4 { propogatePos $1 $ LTEExpr $1 $3 } 
     | Expr3 ">" Expr4 { propogatePos $1 $ GTExpr $1 $3 } 
     | Expr3 ">=" Expr4 { propogatePos $1 $ GTEExpr $1 $3 } 
     | Expr4 { propogatePos $1 $ Expr4 $1 }

Expr4 : Expr4 "+" Expr5 { propogatePos $1 $ AddExpr $1 $3 }
     | Expr4 "-" Expr5 { propogatePos $1 $ SubtractExpr $1 $3 } 
     | Expr5 { propogatePos $1 $ Expr5 $1 }

Expr5 : Expr5 "*" Expr6 { propogatePos $1 $ MultiplyExpr $1 $3 }
     | Expr5 "/" Expr6 { propogatePos $1 $ DivideExpr $1 $3 } 
     | Expr5 "%" Expr6 { propogatePos $1 $ ModuloExpr $1 $3 } 
     | Expr6 { propogatePos $1 $ Expr6 $1 }

Expr6 : "-" Expr7 { propogatePos $1 $ NegateExpr $2 }
     | "!" Expr7 { propogatePos $1 $ NotExpr $2 } 
     | Expr7 { propogatePos $1 $ Expr7 $1 }

Expr7 : Literal { propogatePos $1 $ LiteralExpr $1 }
     | Location { propogatePos $1 $ LocationExpr $1 } 
     | MethodCall { propogatePos $1 $ MethodCallExpr $1 }
     | "(" Expr ")" { propogatePos $1 $ ParenExpr $2 }

-- Maybe flip the recursion direction on this for constant stack space
CommaExprs : Expr { [$1] }
        | Expr "," { [$1] }
        | Expr "," CommaExprs { $1 : $3 }

CommaDecls : id { [propogatePos $1 $ VarDecl (extractPosString $1)] }
         | id "[" int "]" {  [propogatePos $1 $ ArrayDecl (extractPosString $1) (extractPosInt $3)] }
         | id "," {  [propogatePos $1 $ VarDecl (extractPosString $1)] }
         | id "[" int "]" "," { [propogatePos $1 $ ArrayDecl (extractPosString $1) (extractPosInt $3)] }
         | id "," CommaDecls { (propogatePos $1 $ VarDecl (extractPosString $1)) : $3 }
         | id "[" int "]" "," CommaDecls { (propogatePos $1 $ ArrayDecl (extractPosString $1) (extractPosInt $3)) : $6 }

CommaCalloutArgs : CalloutArg { [$1] }
        | CalloutArg "," { [$1] }
        | CalloutArg "," CommaCalloutArgs { $1 : $3 }

CalloutArg : Expr { propogatePos $1 $ ExprCalloutArg $1 }
        | string { propogatePos $1 $ StringCalloutArg $ extractString $1}


Literal : int { propogatePos $1 $ Int $ extractInt $1}
        | bool { propogatePos $1 $ Bool $ extractBool $1}
        | char { propogatePos $1 $ Char $ extractChar $1}


----------------------------------- Haskell -----------------------------------
{

type Pos = (Int, Int)
applyFst :: (a -> b) -> (a, c) -> (b, c)
applyFst f (x,y) = (f x, y)

extractPos :: ScannedToken -> Pos
extractPos st = (line st, column st)

extractBool :: ScannedToken -> Bool
extractBool s@(ScannedToken _ _ (BoolLiteral x)) = x

extractWithPos :: (ScannedToken -> a) -> ScannedToken -> WithPos a
extractWithPos f s = propogatePos s $ f s

extractInt :: ScannedToken -> String
extractInt s@(ScannedToken _ _ (Number x)) = x

extractPosInt = extractWithPos extractInt

extractChar :: ScannedToken -> Char
extractChar s@(ScannedToken _ _ (CharLiteral x)) = x

extractString :: ScannedToken -> String
extractString s@(ScannedToken _ _ (StringLiteral x)) = x

extractPosString = extractWithPos extractString

extractType :: ScannedToken -> Type
extractType s@(ScannedToken _ _ (DataType x)) = Type x

extractPosType = extractWithPos extractType

extractId :: ScannedToken -> String
extractId s@(ScannedToken _ _ (Identifier x)) = x

data WithPos a = P Pos a deriving (Show)

instance Functor WithPos where
    fmap f (P p v) = P p (f v)

getPos :: WithPos a -> Pos
getPos (P p _) = p

changeLine :: Int -> WithPos a -> WithPos a
changeLine n (P (x,y) v) = P (x+n,y) v

changeCol :: Int -> WithPos a -> WithPos a
changeCol n (P (x,y) v) = P (x,y+n) v

getVal :: WithPos a -> a
getVal (P _ v) = v

addPos :: Pos -> a -> WithPos a
addPos p v = P p v

class PropogatePos a where
    propogatePos :: a -> b -> WithPos b

instance PropogatePos (WithPos a) where
    propogatePos wp = addPos (getPos wp)

instance PropogatePos ScannedToken where
    propogatePos st = addPos (line st, column st)


data Program = Program CalloutDecls FieldDecls MethodDecls deriving (Show)
data Block = Block FieldDecls Statements deriving (Show)

data SpaceDecl = VarDecl (WithPos String) | ArrayDecl (WithPos String) (WithPos String) deriving (Show)
data FieldDecl = FieldDecl (WithPos Type) CommaDecls deriving (Show)
data ParamDecl = ParamDecl (WithPos Type) (WithPos String) deriving (Show)
data MethodDecl = MethodDecl (WithPos Type) (WithPos String) ParamDecls (WithPos Block) deriving (Show)
data CalloutDecl = CalloutDecl (WithPos String) deriving (Show)

type CommaDecls = [WithPos SpaceDecl]
type ParamDecls = [WithPos ParamDecl]
type FieldDecls = [WithPos FieldDecl]
type Statements = [WithPos Statement]
type MethodDecls = [WithPos MethodDecl]
type CalloutDecls = [WithPos CalloutDecl]

data Statement = AssignStatement (WithPos Location) (WithPos AssignOp) (WithPos Expr)
        | MethodCallStatement (WithPos MethodCall)
        | IfStatement (WithPos Expr) (WithPos Block)
        | IfElseStatement (WithPos Expr) (WithPos Block) (WithPos Block)
        | ForStatement (WithPos String) (WithPos Expr) (WithPos Expr) (WithPos Block)
        | WhileStatement (WithPos Expr) (WithPos Block)
        | ReturnStatement (WithPos Expr)
        | EmptyReturnStatement
        | BreakStatement
        | ContinueStatement
     deriving (Show)

data Type = Type String
     deriving (Show)

data AssignOp = AssignOp String
     deriving (Show)

data MethodCall = ParamlessMethodCall (WithPos MethodName)
                | ExprParamMethodCall (WithPos MethodName) CommaExprs
                | CalloutParamMethodCall (WithPos MethodName) CommaCalloutArgs
     deriving (Show)

data CalloutArg = ExprCalloutArg (WithPos Expr)
                | StringCalloutArg String
     deriving (Show)

data MethodName = MethodName (WithPos String)
     deriving (Show)


data Location = Location (WithPos String)
          | IndexedLocation (WithPos String) (WithPos Expr)
     deriving (Show)

data Expr = OrExpr (WithPos Expr) (WithPos Expr1)
          | Expr1 (WithPos Expr1)
     deriving (Show)

data Expr1 = AndExpr (WithPos Expr1) (WithPos Expr2)
          | Expr2 (WithPos Expr2)
     deriving (Show)

data Expr2 = EqualExpr (WithPos Expr2) (WithPos Expr3)
          | NotEqualExpr (WithPos Expr2) (WithPos Expr3)
          | Expr3 (WithPos Expr3)
     deriving (Show)

data Expr3 = LTExpr (WithPos Expr3) (WithPos Expr4)
          | LTEExpr (WithPos Expr3) (WithPos Expr4)
          | GTExpr (WithPos Expr3) (WithPos Expr4)
          | GTEExpr (WithPos Expr3) (WithPos Expr4)
          | Expr4 (WithPos Expr4)
     deriving (Show)

data Expr4 = AddExpr (WithPos Expr4) (WithPos Expr5)
          | SubtractExpr (WithPos Expr4) (WithPos Expr5)
          | Expr5 (WithPos Expr5)
     deriving (Show)

data Expr5 = MultiplyExpr (WithPos Expr5) (WithPos Expr6)
          | DivideExpr (WithPos Expr5) (WithPos Expr6)
          | ModuloExpr (WithPos Expr5) (WithPos Expr6)
          | Expr6 (WithPos Expr6)
     deriving (Show)

data Expr6 = NegateExpr (WithPos Expr7)
          | NotExpr (WithPos Expr7)
          | Expr7 (WithPos Expr7)
     deriving (Show)

data Expr7 = LiteralExpr (WithPos Literal)
          | LocationExpr (WithPos Location)
          | MethodCallExpr (WithPos MethodCall)
          | ParenExpr (WithPos Expr)
     deriving (Show)

type CommaExprs = [WithPos Expr]
type CommaCalloutArgs = [WithPos CalloutArg]

data Literal = Bool Bool | Int String | Char Char
     deriving (Show)

parseError :: [ScannedToken] -> Either String a
parseError [] = Left "unexpected EOF"
parseError toks =
  Left $ printf "line %d:%d: unexpected token%s '%s'"
                lineNo
                columnNo
                (if (not $ null $ tail toks) then "s" else "")
                badTokenText
  where firstBadToken = head toks
        lineNo = Scanner.line firstBadToken
        columnNo = Scanner.column firstBadToken
        badTokenText = concatMap (show . extractRawToken) toks
}
