-- Scanner -- Decaf scanner                                     -*- haskell -*-
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
{-# OPTIONS_GHC -w #-}
module Scanner ( ScannedToken(..)
               , Token(..)
               , scan
               , formatTokensAndErrors
               ) where
}

%wrapper "6.035"


----------------------------------- Tokens ------------------------------------

$digit = [0-9]
$alpha = [a-zA-Z_]
$alphanum = [$alpha $digit]
$hexDigit = [0-9A-Fa-f]
$escapeChars = [t n \' \\ \"] 
$opchars = []
$eqchars = []
$symbols = [\* \+ \- \/ \% = ! \< \> \[ \] \( \) \;]
$literalTrailers = [$white $symbols]
-- "
@keywords = class | boolean | break | callout | continue | else | false | for | while | if | int | return | true | void
@statementMarker = if | for | while | return | break | continue

tokens :-
  $white+ ;
  "//".*  ;                     -- comment

  -- Reserved words

  if { \posn s -> scannedToken posn If }
  for { \posn s -> scannedToken posn For }
  while { \posn s -> scannedToken posn While }
  return { \posn s -> scannedToken posn Return }
  break { \posn s -> scannedToken posn Break }
  continue { \posn s -> scannedToken posn Continue }
  else { \posn s -> scannedToken posn Else }
  void { \posn s -> scannedToken posn Void }
  callout { \posn s -> scannedToken posn Callout }

  -- @statementMarker   { \posn s -> scannedToken posn $ StatementMarker s }

  -- Operators of various types
  == { \posn s -> scannedToken posn $ EqOp Equal }
  != { \posn s -> scannedToken posn $ EqOp NEqual }

  && { \posn s -> scannedToken posn $ CondOp And }
  \| \| { \posn s -> scannedToken posn $ CondOp Or }

  = { \posn s -> scannedToken posn $ AssignOp SetOp }
  \+ ={ \posn s -> scannedToken posn $ AssignOp SetPlusOp }
  \- ={ \posn s -> scannedToken posn $ AssignOp SetMinusOp }

  \< { \posn s -> scannedToken posn $ RelOp LessT }
  \> { \posn s -> scannedToken posn $ RelOp GreaterT }
  \< = { \posn s -> scannedToken posn $ RelOp LessTE }
  \> = { \posn s -> scannedToken posn $ RelOp GreaterTE }

  \+  { \posn s -> scannedToken posn $ ArithOp Add }
  \- { \posn s -> scannedToken posn $ ArithOp Subtract }
  \* { \posn s -> scannedToken posn $ ArithOp Multiply }
  \/ { \posn s -> scannedToken posn $ ArithOp Divide }
  \% { \posn s -> scannedToken posn $ ArithOp Modulo }

  -- The only two types supported: boolean and int
  int { \posn s -> scannedToken posn $ DataType s } 
  boolean { \posn s -> scannedToken posn $ DataType s } 

  -- Character literals
  \' $printable # [\' \" \\] \'  { \posn s -> scannedToken posn $ CharLiteral (s !! 1) }
  \' \\ $escapeChars \'  { \posn s -> scannedToken posn $ CharLiteral $ parseEscapeChar (s !! 2) }

  -- Hex literals
  0x $hexDigit+ / $literalTrailers     { \posn s -> scannedToken posn $ Number s } 

  -- Number literals
  $digit+ / $literalTrailers  { \posn s -> scannedToken posn $ Number s } 

  -- Unary minus symbol 
  \- { \posn s -> scannedToken posn $ MinusSymbol } 

  -- Bool Literals
  true { \posn s -> scannedToken posn $ BoolLiteral True }
  false { \posn s -> scannedToken posn $ BoolLiteral False }

  -- String literals
  \" ( (\\ $escapeChars)? | ($printable # [\\ \' \"])? )* \"   { \posn s -> scannedToken posn $ StringLiteral $ unescapeString $ init $ tail s }


  \{        { \posn _ -> scannedToken posn LCurly }
  \;        { \posn _ -> scannedToken posn SemiColon }
  \!        { \posn _ -> scannedToken posn Not }
  \}        { \posn _ -> scannedToken posn RCurly }
  \[        { \posn _ -> scannedToken posn LSquare }
  \]        { \posn _ -> scannedToken posn RSquare }
  \(        { \posn _ -> scannedToken posn LParen }
  \)        { \posn _ -> scannedToken posn RParen }

  -- Identifiers
  $alpha $alphanum*  { \posn s -> scannedToken posn $ Identifier s }


----------------------------- Representing tokens -----------------------------

{

-- | A token with position information.
data ScannedToken = ScannedToken { line :: Int
                                 , column :: Int
                                 , extractRawToken :: Token
                                 } deriving (Eq)


data ArithOpType = Add | Subtract | Multiply | Divide | Modulo deriving (Eq)

instance Show ArithOpType where
    show Add = "+"
    show Subtract = "-"
    show Multiply = "*"
    show Divide = "/"
    show Modulo = "%"

data RelOpType = LessT | LessTE | GreaterT | GreaterTE deriving (Eq, Ord)

instance Show RelOpType where
    show LessT = "<"
    show LessTE = "<="
    show GreaterT = ">="
    show GreaterTE = ">"
 
data AssignOpType = SetOp | SetPlusOp | SetMinusOp deriving (Eq)

instance Show AssignOpType where
    show SetOp = "="
    show SetPlusOp = "+="
    show SetMinusOp = "-="
 
data EqOpType = Equal | NEqual deriving (Eq, Ord)

instance Show EqOpType where
    show Equal = "=="
    show NEqual = "!="

data CondOpType = And | Or deriving (Eq)

instance Show CondOpType where
    show And = "&&"
    show Or = "||"

-- | A token.
data Token = Keyword String
           | Identifier String
           | DataType String
           | CharLiteral Char
           | StringLiteral String
           | BoolLiteral Bool
           | Not
           | Number String
           | StatementMarker String
           | If
           | For
           | While
           | Return
           | Break
           | Continue
           | Else
           | Void
           | Callout
           | ArithOp ArithOpType
           | AssignOp AssignOpType
           | EqOp EqOpType
           | RelOp RelOpType
           | CondOp CondOpType
           | LCurly
           | RCurly
           | LParen
           | RParen
           | LSquare
           | RSquare
           | SemiColon
           | MinusSymbol
           deriving (Eq)

showOrigChar :: Char -> String
showOrigChar '\t' = "\\t"
showOrigChar '\\' = "\\\\"
showOrigChar '\'' = "\\\'"
showOrigChar '\"' = "\\\""
showOrigChar '\n' = "\\n"
showOrigChar x = [x]

instance Show Token where
  show (Keyword k) = k
  show (StatementMarker k) = k
  show (Identifier s) = "IDENTIFIER " ++ s
  show (CharLiteral c) = "CHARLITERAL \'" ++ showOrigChar c ++ "\'"
  show (BoolLiteral b) = "BOOLEANLITERAL " ++ (map toLower . show) b
  show (StringLiteral s) = "STRINGLITERAL \"" ++ (concat . map showOrigChar) s ++ "\""
  show (Number s) = "INTLITERAL " ++ s
  show (ArithOp o) = show o
  show (RelOp o) = show o
  show (EqOp o) = show o
  show (AssignOp o) = show o
  show (CondOp o) = show o
  show LCurly = "{"
  show RCurly = "}"
  show LParen = "("
  show RParen = ")"
  show LSquare = "["
  show RSquare = "]"
  show SemiColon = ";"
  show MinusSymbol = "-"
  show Not = "!"
  show (DataType t) = t
  show If = "if"
  show For = "for"
  show While = "while"
  show Return = "return"
  show Break = "break"
  show Continue = "continue"
  show Else = "else"
  show Void = "void"
  show Callout = "callout"

{-| Smart constructor to create a 'ScannedToken' by extracting the line and
column numbers from an 'AlexPosn'. -}
scannedToken :: AlexPosn -> Token -> ScannedToken
scannedToken (AlexPn _ lineNo columnNo) tok = ScannedToken lineNo columnNo tok

parseEscapeChar :: Char -> Char
parseEscapeChar 't' = '\t'
parseEscapeChar 'n' = '\n'
parseEscapeChar c = c

unescapeString :: String -> String
unescapeString [] = []
unescapeString ('\\':c:cs) = (parseEscapeChar c):(unescapeString cs)
unescapeString (c1:c2:cs) = c1:(unescapeString (c2:cs))
unescapeString [c] = [c]


---------------------------- Scanning entry point -----------------------------

scan :: String -> [Either String ScannedToken]
scan = alexScanTokens

formatTokensAndErrors :: [Either String ScannedToken] -> String
formatTokensAndErrors = unlines . map formatTokenOrError
  where formatTokenOrError tokenOrError =
          case tokenOrError of
            Left err -> err
            Right tok -> unwords [ show $ line tok
                                 , show $ extractRawToken tok
                                 ]
}
