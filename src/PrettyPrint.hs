module PrettyPrint where

import Text.PrettyPrint.HughesPJ

class PrettyPrint a where
    ppr :: a -> Doc
    pPrint :: a -> String
    pprIO :: a -> IO ()
    pPrint = render . ppr
    ppr = text . pPrint
    pprIO = putStrLn . render . ppr


instance (PrettyPrint a) => PrettyPrint (Maybe a) where
    ppr Nothing = text "Nothing!"
    ppr (Just x) = ppr x

instance PrettyPrint Char where
    ppr a = text [a]

instance PrettyPrint Int where
    ppr = int

instance PrettyPrint Float where
    ppr = float

instance PrettyPrint Double where
    ppr = double

instance PrettyPrint Integer where
    ppr = integer
