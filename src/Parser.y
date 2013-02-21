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
  '{'        { ScannedToken _ _ LCurly }
  '}'        { ScannedToken _ _ RCurly }
  '('        { ScannedToken _ _ LParen }
  ')'        { ScannedToken _ _ RParen }
  '['        { ScannedToken _ _ LSquare }
  ']'        { ScannedToken _ _ RSquare }
  ';'        { ScannedToken _ _ SemiColon }
  '!'        { ScannedToken _ _ Not }
  '-'        { ScannedToken _ _ MinusSymbol }

  bool { ScannedToken _ _ (BoolLiteral $$) }
  string { ScannedToken _ _ (StringLiteral $$) }
  char { ScannedToken _ _ (CharLiteral $$) }
  int { ScannedToken _ _ (Number $$) }

  arith_op { ScannedToken _ _ (ArithOp $$) }
  rel_op { ScannedToken _ _ (RelOp $$) }
  eq_op { ScannedToken _ _ (EqOp $$) }
  assign_op { ScannedToken _ _ (AssignOp $$) }
  cond_op { ScannedToken _ _ (CondOp $$) }

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

Expr : Literal { LiteralExpr $1 }
        | Expr BinOp Expr { CombinedExpr $2 $1 $3  }
        | '-' Expr { NegatedExpr $2 }
        | '!' Expr { NotExpr $2 }
        | '(' Expr ')' { ParenExpr $2 }


BinOp : arith_op { BinOp (show $1) }
        | rel_op { BinOp (show $1) }
        | eq_op { BinOp (show $1) }
        | cond_op { BinOp (show $1) }
        | '-' { BinOp "-"}


Literal : int { Int $1 }
        | bool { Bool $1 }
        | char { Char $1 }


----------------------------------- Haskell -----------------------------------
{

data Expr = LiteralExpr Literal
          | CombinedExpr BinOp Expr Expr
          | NegatedExpr Expr
          | NotExpr Expr
          | ParenExpr Expr
data BinOp = BinOp String
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
