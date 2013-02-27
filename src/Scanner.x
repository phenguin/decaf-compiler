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
import Data.Char (toLower)
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
$symbols = [\* \+ \- \/ \% = ! \< \> \[ \] \( \) \; \,]
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

  -- Operators of various types
--  == { \posn s -> scannedToken posn $ EqualSym}
--  != { \posn s -> scannedToken posn $ NotEqualSym }
--
--  && { \posn s -> scannedToken posn $ AndSym }
--  \| \| { \posn s -> scannedToken posn $ OrSym }
--
--  = { \posn s -> scannedToken posn $ SetSym }
--  \+ ={ \posn s -> scannedToken posn $ SetPlusSym }
--  \- ={ \posn s -> scannedToken posn $ SetMinusSym }
--
--  \< { \posn s -> scannedToken posn $ LessThanSym }
--  \> { \posn s -> scannedToken posn $ GreaterThanSym }
--  \< = { \posn s -> scannedToken posn $ LessThanOrESym }
--  \> = { \posn s -> scannedToken posn $ GreaterThanOrESym }
--
--  \+  { \posn s -> scannedToken posn $ AddSym }
--  \* { \posn s -> scannedToken posn $ MultiplySym }
--  \/ { \posn s -> scannedToken posn $ DivideSym }
--  \% { \posn s -> scannedToken posn $ ModuloSym }

  == { \posn s -> scannedToken posn $ (Symbol "==")}
  != { \posn s -> scannedToken posn $ (Symbol "!=") }

  && { \posn s -> scannedToken posn $ (Symbol "&&") }
  \| \| { \posn s -> scannedToken posn $ (Symbol "||" ) }

  = { \posn s -> scannedToken posn $ (Symbol "=" ) }
  \+ ={ \posn s -> scannedToken posn $ (Symbol "+=") }
  \- ={ \posn s -> scannedToken posn $ (Symbol "-=") }

  \< { \posn s -> scannedToken posn $ (Symbol "<" ) }
  \> { \posn s -> scannedToken posn $ (Symbol ">" ) }
  \< = { \posn s -> scannedToken posn $ (Symbol "<=" ) }
  \> = { \posn s -> scannedToken posn $ (Symbol ">=" ) }

  \+  { \posn s -> scannedToken posn $ (Symbol "+"  ) }
  \* { \posn s -> scannedToken posn $ (Symbol "*" ) }
  \/ { \posn s -> scannedToken posn $ (Symbol "/" ) }
  \% { \posn s -> scannedToken posn $ (Symbol "%" ) }

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
  \- { \posn s -> scannedToken posn $ (Symbol "-") } 

  -- Bool Literals
  true { \posn s -> scannedToken posn $ BoolLiteral True }
  false { \posn s -> scannedToken posn $ BoolLiteral False }

  -- String literals
  \" ( (\\ $escapeChars)? | ($printable # [\\ \' \"])? )* \"   { \posn s -> scannedToken posn $ StringLiteral $ unescapeString $ init $ tail s }


  \{        { \posn _ -> scannedToken posn LCurly }
  \;        { \posn _ -> scannedToken posn SemiColon }
  \,        { \posn _ -> scannedToken posn Comma }
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

-- | A token.
data Token = Identifier String
           | DataType String
           | CharLiteral Char
           | StringLiteral String
           | BoolLiteral Bool
           | Not
           | Number String
           | If
           | For
           | While
           | Return
           | Break
           | Continue
           | Else
           | Void
           | Callout
           | Symbol String
           | LCurly
           | RCurly
           | LParen
           | RParen
           | LSquare
           | RSquare
           | SemiColon
           | Comma
           deriving (Eq)

showOrigChar :: Char -> String
showOrigChar '\t' = "\\t"
showOrigChar '\\' = "\\\\"
showOrigChar '\'' = "\\\'"
showOrigChar '\"' = "\\\""
showOrigChar '\n' = "\\n"
showOrigChar x = [x]

instance Show Token where
  show (Identifier s) = "IDENTIFIER " ++ s
  show (CharLiteral c) = "CHARLITERAL \'" ++ showOrigChar c ++ "\'"
  show (BoolLiteral b) = "BOOLEANLITERAL " ++ (map toLower . show) b
  show (StringLiteral s) = "STRINGLITERAL \"" ++ (concat . map showOrigChar) s ++ "\""
  show (Number s) = "INTLITERAL " ++ s
  show LCurly = "{"
  show RCurly = "}"
  show LParen = "("
  show RParen = ")"
  show LSquare = "["
  show RSquare = "]"
  show SemiColon = ";"
  show Comma = ","
  show (Symbol s) = s
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
