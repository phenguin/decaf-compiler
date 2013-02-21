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
  ret { ScannedToken _ _ Return }
  break_st { ScannedToken _ _ Break }
  continue { ScannedToken _ _ Continue }
  else { ScannedToken _ _ Else }
  void { ScannedToken _ _ Void }
  callout { ScannedToken _ _ Callout }

%% -------------------------------- Grammar -----------------------------------

MethodCall : MethodName "(" CommaExprs ")" { ExprParamMethodCall $1 $3 }
        | MethodName "(" CommaCalloutArgs ")" { CalloutParamMethodCall $1 $3 }

MethodName : id { MethodName $1 }

Location : id { Location $1 }
        | id "[" Expr "]" { IndexedLocation $1 $3 }

-- Expr : Literal { LiteralExpr $1 }
--         | Expr BinOp Expr { CombinedExpr $2 $1 $3  }
--         | "-" Expr { NegatedExpr $2 }
--         | MethodCall { MethodCallExpr $1 }
--         | Location { LocationExpr $1 }
--         | "!" Expr { NotExpr $2 }
--         | "(" Expr ")" { ParenExpr $2 }

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

Expr7 : Literal { LiteralExpr $1 $3 }
     | Location { LocationExpr $1 $3 } 
     | MethodCall { MethodCallExpr $1 }
     | "(" Expr ")" { ParenExpr $1 }

-- Maybe flip the recursion direction on this for constant stack space
CommaExprs : Expr { [$1] }
        | Expr "," { [$1] }
        | Expr "," CommaExprs { $1 : $3 }

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

data MethodCall = ExprParamMethodCall MethodName CommaExprs
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
