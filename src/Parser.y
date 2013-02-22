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
module Parser ( parse
              ) where

import Text.Printf (printf)

import Scanner (ScannedToken(..), Token(..))

}


--------------------------------- Directives ----------------------------------

%name parse
%error { parseError }
%monad { Either String }

%tokentype { ScannedToken }

%token
  id { ScannedToken _ _ (Identifier $$) }
  "{"        { ScannedToken _ _ LCurly }
  "}"        { ScannedToken _ _ RCurly }
  "("        { ScannedToken _ _ LParen }
  ")"        { ScannedToken _ _ RParen }
  "["        { ScannedToken _ _ LSquare }
  "]"        { ScannedToken _ _ RSquare }
  ";"        { ScannedToken _ _ SemiColon }
  "!"        { ScannedToken _ _ Not }
  ","        { ScannedToken _ _ Comma }

  bool { ScannedToken _ _ (BoolLiteral $$) }
  string { ScannedToken _ _ (StringLiteral $$) }
  char { ScannedToken _ _ (CharLiteral $$) }
  int { ScannedToken _ _ (Number $$) }

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

  data_type { ScannedToken _ _ (DataType $$) }
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

Program : CalloutDecls FieldDecls MethodDecls {}

MethodDecls : {- empty -} { [] }
            | MethodDecl MethodDecls { $1 : $2 }

MethodDecl : Type id "(" ")" Block { MethodDecl $1 $2 [] $5 }
           | Type id "(" ParamDecls ")" Block { MethodDecl $1 $2 $4 $6 }
           | void id "(" ")" Block { MethodDecl (Type "void") $2 [] $5 }
           | void id "(" ParamDecls ")" Block { MethodDecl (Type "void") $2 $4 $6 }

Type : data_type { Type $1 }

FieldDecl : Type CommaDecls ";" { FieldDecl $1 $2 }

FieldDecls : {- empty -} { [] }
           | FieldDecls FieldDecl { $2 : $1 }

CalloutDecl : callout id ";" { CalloutDecl $2 }

CalloutDecls : {- empty -} { [] }
             | CalloutDecl CalloutDecls { $1 : $2 }

Block : "{" FieldDecls Statements "}" { Block $2 $3 }
      | "{" Statements "}" { Block [] $2 }

ParamDecl : Type id { ParamDecl $1 $2 }

ParamDecls : ParamDecl { [$1] }
           | ParamDecl "," { [$1] }
           | ParamDecl "," ParamDecls { $1 : $3 }

Statement : Location AssignOp Expr ";" { AssignStatement $1 $2 $3 }
        | MethodCall ";" { MethodCallStatement $1 }
        | if "(" Expr ")" Block { IfStatement $3 $5 }
        | if "(" Expr ")" Block else Block { IfElseStatement $3 $5 $7 }
        | for "(" id "=" Expr ";" Expr ")" Block { ForStatement $3 $5 $7 $9 }
        | while "(" Expr ")" Block { WhileStatement $3 $5 }
        | return Expr ";" { ReturnStatement $2 }
        | return ";" { EmptyReturnStatement }
        | break ";" { BreakStatement }
        | continue ";" { ContinueStatement }

Statements : {- empty -} { [] }
           | Statement Statements { $1 : $2 }

AssignOp : "=" { AssignOp "=" }
        | "+=" { AssignOp "+=" }
        | "-=" { AssignOp "-=" }

MethodCall : MethodName "(" ")" { ParamlessMethodCall $1 }
        | MethodName "(" CommaExprs ")" { ExprParamMethodCall $1 $3 }
        | MethodName "(" CommaCalloutArgs ")" { CalloutParamMethodCall $1 $3 }

MethodName : id { MethodName $1 }

Location : id { Location $1 }
        | id "[" Expr "]" { IndexedLocation $1 $3 }

-- Order of operations stuff
Expr : Expr "||" Expr1 { OrExpr $1 $3 }
     | Expr1 { Expr1 $1 }

Expr1 : Expr1 "&&" Expr2 { AndExpr $1 $3 }
     | Expr2 { Expr2 $1 }

Expr2 : Expr2 "==" Expr3 { EqualExpr $1 $3 }
     | Expr2 "!=" Expr3 { NotEqualExpr $1 $3 } 
     | Expr3 { Expr3 $1 }

Expr3 : Expr3 "<" Expr4 { LTExpr $1 $3 }
     | Expr3 "<=" Expr4 { LTEExpr $1 $3 } 
     | Expr3 ">" Expr4 { GTExpr $1 $3 } 
     | Expr3 ">=" Expr4 { GTEExpr $1 $3 } 
     | Expr4 { Expr4 $1 }

Expr4 : Expr4 "+" Expr5 { AddExpr $1 $3 }
     | Expr4 "-" Expr5 { SubtractExpr $1 $3 } 
     | Expr5 { Expr5 $1 }

Expr5 : Expr5 "*" Expr6 { MultiplyExpr $1 $3 }
     | Expr5 "/" Expr6 { DivideExpr $1 $3 } 
     | Expr5 "%" Expr6 { ModuloExpr $1 $3 } 
     | Expr6 { Expr6 $1 }

Expr6 : "-" Expr7 { NegateExpr $2 }
     | "!" Expr7 { NotExpr $2 } 
     | Expr7 { Expr7 $1 }

Expr7 : Literal { LiteralExpr $1 }
     | Location { LocationExpr $1 } 
     | MethodCall { MethodCallExpr $1 }
     | "(" Expr ")" { ParenExpr $2 }

-- Maybe flip the recursion direction on this for constant stack space
CommaExprs : Expr { [$1] }
        | Expr "," { [$1] }
        | Expr "," CommaExprs { $1 : $3 }

CommaDecls : id { [VarDecl $1] }
         | id "[" int "]" { [ArrayDecl $1 $3] }
         | id "," { [VarDecl $1] }
         | id "[" int "]" "," { [ArrayDecl $1 $3] }
         | id "," CommaDecls { (VarDecl $1) : $3 }
         | id "[" int "]" "," CommaDecls { (ArrayDecl $1 $3) : $6 }

CommaCalloutArgs : CalloutArg { [$1] }
        | CalloutArg "," { [$1] }
        | CalloutArg "," CommaCalloutArgs { $1 : $3 }

CalloutArg : Expr { ExprCalloutArg $1 }
        | string { StringCalloutArg $1}


Literal : int { Int $1 }
        | bool { Bool $1 }
        | char { Char $1 }


----------------------------------- Haskell -----------------------------------
{

-- data Program = Program CalloutDecls FieldDecls MethodDecls
data Program1 = Program1 MethodDecls
data Block = Block FieldDecls Statements

data SpaceDecl = VarDecl String | ArrayDecl String String
data FieldDecl = FieldDecl Type CommaDecls
data ParamDecl = ParamDecl Type String
data MethodDecl = MethodDecl Type String ParamDecls Block
data CalloutDecl = CalloutDecl String

type CommaDecls = [SpaceDecl]
type ParamDecls = [ParamDecl]
type FieldDecls = [FieldDecl]
type Statements = [Statement]
type MethodDecls = [MethodDecl]
type CalloutDecls = [CalloutDecl]


data Statement = AssignStatement Location AssignOp Expr
        | MethodCallStatement MethodCall
        | IfStatement Expr Block
        | IfElseStatement Expr Block Block
        | ForStatement String Expr Expr Block
        | WhileStatement Expr Block
        | ReturnStatement Expr
        | EmptyReturnStatement
        | BreakStatement
        | ContinueStatement

data Type = Type String

data AssignOp = AssignOp String

data MethodCall = ParamlessMethodCall MethodName
                | ExprParamMethodCall MethodName CommaExprs
                | CalloutParamMethodCall MethodName CommaCalloutArgs

data CalloutArg = ExprCalloutArg Expr
                | StringCalloutArg String

data MethodName = MethodName String


data Location = Location String
          | IndexedLocation String Expr

data Expr = OrExpr Expr Expr1
          | Expr1 Expr1

data Expr1 = AndExpr Expr1 Expr2
          | Expr2 Expr2

data Expr2 = EqualExpr Expr2 Expr3
          | NotEqualExpr Expr2 Expr3
          | Expr3 Expr3

data Expr3 = LTExpr Expr3 Expr4
          | LTEExpr Expr3 Expr4
          | GTExpr Expr3 Expr4
          | GTEExpr Expr3 Expr4
          | Expr4 Expr4

data Expr4 = AddExpr Expr4 Expr5
          | SubtractExpr Expr4 Expr5
          | Expr5 Expr5

data Expr5 = MultiplyExpr Expr5 Expr6
          | DivideExpr Expr5 Expr6
          | ModuloExpr Expr5 Expr6
          | Expr6 Expr6

data Expr6 = NegateExpr Expr7
          | NotExpr Expr7
          | Expr7 Expr7

data Expr7 = LiteralExpr Literal
          | LocationExpr Location
          | MethodCallExpr MethodCall
          | ParenExpr Expr

type CommaExprs = [Expr]
type CommaCalloutArgs = [CalloutArg]

data BinOp = BinOp ScannedToken

data Literal = Bool Bool | Int String | Char Char

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
