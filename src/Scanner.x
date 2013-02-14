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

$alpha = [a-zA-Z]

tokens :-
  $white+ ;
  "//".*  ;                     -- comment
  class   { \posn s -> scannedToken posn $ Keyword s }
  \{      { \posn _ -> scannedToken posn LCurly }
  \}      { \posn _ -> scannedToken posn RCurly }
  $alpha+ { \posn s -> scannedToken posn $ Identifier s }


----------------------------- Representing tokens -----------------------------

{
-- | A token with position information.
data ScannedToken = ScannedToken { line :: Int
                                 , column :: Int
                                 , extractRawToken :: Token
                                 } deriving (Eq)

-- | A token.
data Token = Keyword String
           | Identifier String
           | LCurly
           | RCurly
           deriving (Eq)
instance Show Token where
  show (Keyword k) = k
  show (Identifier s) = "IDENTIFIER " ++ s
  show LCurly = "{"
  show RCurly = "}"

{-| Smart constructor to create a 'ScannedToken' by extracting the line and
column numbers from an 'AlexPosn'. -}
scannedToken :: AlexPosn -> Token -> ScannedToken
scannedToken (AlexPn _ lineNo columnNo) tok = ScannedToken lineNo columnNo tok


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
