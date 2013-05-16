{-# LANGUAGE DeriveDataTypeable #-}
module Varmarker where

import PrettyPrint
import Data.Char (toLower)
import Data.Generics
import Text.PrettyPrint.HughesPJ
import qualified Transforms

data VarMarker = VarMarker {
    varName :: String,
    varType :: Transforms.FDType,
    varScope :: [Scoped]
    } | Precolored deriving (Show, Eq, Ord, Data, Typeable)

data Color = CRCX | CRDX | CRSI | CRDI | CR8 | CR9 | CRSP | CRBP | CRAX | CRBX | CR10 | CR11 | CR12 | CR13 | CR14 | CR15 deriving (Eq, Show, Ord, Enum, Data, Typeable)

instance PrettyPrint Color where
    ppr = text . ('%':) . tail . map toLower . show

data Scoped = Temp | Global | Func String | Loop String 
		deriving (Show,Eq,Ord, Data, Typeable)

allColors = [CRBX .. CR15]

numColors :: Integer
numColors = fromIntegral $ length allColors

setScope :: [Scoped] -> VarMarker -> VarMarker
setScope s (VarMarker n t _) = VarMarker n t s

isArray :: VarMarker -> Bool
isArray (VarMarker _ (Transforms.Array _) _) = True
isArray _ = False

isScoped :: VarMarker -> Bool
isScoped (VarMarker _ _ []) = False
isScoped _ = True

instance PrettyPrint VarMarker where
    ppr (VarMarker name Transforms.Single _) = text name
    ppr (VarMarker name (Transforms.Array _) _) = text name <> lbrack <> rbrack
