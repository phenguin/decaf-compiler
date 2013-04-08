module PrettyPrint where

import Text.PrettyPrint.HughesPJ
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

instance PrettyPrint Char where
    ppr a = text [a]

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (a,b) where
    ppr (a,b) = lparen <+> ppr a <> comma <+> ppr b  <+> rparen

instance (PrettyPrint a, PrettyPrint b, PrettyPrint c) => PrettyPrint (a,b,c) where
    ppr (a,b,c) = lparen <+> ppr a <> comma <+> ppr b <> comma <+> ppr c <+> rparen

instance PrettyPrint Int where
    ppr = int

instance (PrettyPrint a) => PrettyPrint [a] where
    ppr xs = lbrack $$ ppr' xs $$ rbrack
       where ppr' [] = text ""
             ppr' (x:xs) = ppr x <> comma $$
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
