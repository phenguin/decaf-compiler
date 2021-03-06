module PrettyPrint where

import Text.PrettyPrint.HughesPJ
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as M

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

instance PrettyPrint Bool where
    ppr True = text "True"
    ppr False = text "False"

instance PrettyPrint Char where
    ppr a = text [a]

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (a,b) where
    ppr (a,b) = lparen <+> ppr a <> comma <+> ppr b  <+> rparen

instance (PrettyPrint a, PrettyPrint b, PrettyPrint c) => PrettyPrint (a,b,c) where
    ppr (a,b,c) = lparen <+> ppr a <> comma <+> ppr b <> comma <+> ppr c <+> rparen

instance PrettyPrint Int where
    ppr = int

instance (Show a, PrettyPrint a) => PrettyPrint [a] where
    ppr xs = text "[" <+> ppr' xs <> text "]"
       where ppr' [] = text ""
             ppr' (x:xs) = ppr x <> comma <+>
                           ppr' xs

instance (PrettyPrint a) => PrettyPrint (Set a) where
    ppr set = let xs = Set.toList set in text "{" <+> ppr' xs <> text "}"
       where ppr' [] = text ""
             ppr' (x:xs) = ppr x <> comma <+>
                           ppr' xs

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (M.Map a b) where
    ppr mp = foldl f (text "") $ M.toList mp
        where f doc (key, val) = doc $$ ppr key <+> text "->" <+> ppr val

instance PrettyPrint Float where
    ppr = float

instance PrettyPrint Double where
    ppr = double

instance PrettyPrint Integer where
    ppr = integer
