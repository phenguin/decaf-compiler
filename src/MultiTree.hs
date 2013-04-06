module MultiTree where

import Prelude hiding (mapM)
import Control.Monad hiding (mapM)
import Control.Monad.State hiding (mapM)
import PrettyPrint
import Data.Maybe 
import Control.Applicative
import Data.Monoid(Monoid(..))
import Data.Traversable (Traversable(traverse), mapM)
import Data.Foldable (Foldable(foldMap))

data MultiTree a = MT { nodeName :: a, children :: (Forest a) } deriving (Eq)

data Cxt a = Cxt { parentLabel :: a, lefts :: [MultiTree a], rights :: [MultiTree a] } deriving (Eq, Show)

type Forest a = [MultiTree a]

type Context a = [Cxt a]
newtype FocusedMultiTree a = FMT { extractFMT :: (MultiTree a, Context a) } deriving (Eq)

pPrintTabbed :: (Show a) => MultiTree a -> String
pPrintTabbed = pPrintTabbed' 0
    where pPrintTabbed' n (MT x ts) = replicate (2*n) ' ' ++ show x ++ "\n" ++ (concat $ map (pPrintTabbed' (n+1)) ts)

-- Turn tree into a list, order not preserved in a meaningful way
listify :: MultiTree a -> [a]
listify t = (nodeName t) : (concat $ map listify (children t))

instance (Show a) => Show (FocusedMultiTree a) where
    show (FMT t) = show t

-- Stolen from standard Data.Tree
instance Applicative MultiTree where
  pure x = MT x []
  MT f tfs <*> tx@(MT x txs) =
    MT (f x) (map (f <$>) txs ++ map (<*> tx) tfs)

instance Traversable MultiTree where
  traverse f (MT x ts) = MT <$> f x <*> traverse (traverse f) ts

instance Foldable MultiTree where
  foldMap f (MT x ts) = f x `mappend` foldMap (foldMap f) ts

instance (Show a) => Show (MultiTree a) where
    show (MT a []) = show a
    show (MT a ts) = show a ++ " : " ++ show ts

instance Functor MultiTree where
    fmap f (MT a ts)  = MT (f a) (map (fmap f) ts)

instance Functor Cxt where
    fmap f (Cxt a lefts rights) = Cxt (f a) (fmap (fmap f) lefts) (fmap (fmap f) rights)

instance Functor FocusedMultiTree where
    fmap f (FMT (t, cs)) = FMT (fmap f t, map (fmap f) cs)

instance (Show a) => PrettyPrint (FocusedMultiTree a) where
    pPrint = drawTree . removeFocus .alterFocus (\x -> "<" ++ x ++ ">") . fmap show

instance (Show a) => PrettyPrint (MultiTree a) where
    pPrint = drawTree . fmap show

singleton :: a -> MultiTree a
singleton x = MT x []

addChild :: MultiTree a -> MultiTree a -> MultiTree a
addChild t (MT x ts) = MT x (t:ts)

mapOnMatch :: (Functor f) => (a -> Bool) -> (a -> a) -> f a -> f a
mapOnMatch pred f = fmap (\x -> if pred x then f x else x)

unfoldTree :: (b -> (a, [b])) -> b -> MultiTree a
unfoldTree f b = MT a (map (unfoldTree f) bs)
    where (a, bs) = f b

unfoldTreeM :: (Monad m) => (b -> m (a, [b])) -> b -> m (MultiTree a)
unfoldTreeM f b = do
    (a, bs) <- f b
    ts <- mapM (unfoldTreeM f) bs
    return (MT a ts)

-- FocusedMultiTree navigation

focusedTree :: MultiTree a -> FocusedMultiTree a
focusedTree t = FMT (t, [])

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:xs) = Just x

goDown :: Int -> FocusedMultiTree a -> Maybe (FocusedMultiTree a)
goDown n (FMT (MT x ts, cs)) = let (lefts, rights) = splitAt n ts in do
        focus <- safeHead rights
        return $ FMT (focus, (Cxt x (reverse lefts) (tail rights)) : cs)

goUp :: FocusedMultiTree a -> Maybe (FocusedMultiTree a)
goUp (FMT (t, cs)) = do
    cxt <- safeHead cs
    return $ FMT (MT (parentLabel cxt) (reverse (lefts cxt) ++ [t] ++ rights cxt),
            tail cs)

goLeft :: FocusedMultiTree a -> Maybe (FocusedMultiTree a)
goLeft (FMT (t, cs)) = do
    (Cxt label lefts rights) <- safeHead cs
    focus <- safeHead $ lefts
    return $ FMT (focus, (Cxt label (tail lefts) (t:rights)):(tail cs))

-- SHouldn't need (eq a) here.. 

exhaustDir :: (Eq a) => (FocusedMultiTree a -> Maybe (FocusedMultiTree a)) -> FocusedMultiTree a -> Maybe (FocusedMultiTree a)
exhaustDir navf = exhaustDirs [navf]

exhaustDirs :: (Eq a) => [(FocusedMultiTree a -> Maybe (FocusedMultiTree a))] -> FocusedMultiTree a -> Maybe (FocusedMultiTree a)
exhaustDirs fs = exhaustDirs' fs . return
     where exhaustDirs' fs fmt = let newfmt = fmt >>= (composeM fs) in (if newfmt == Nothing then fmt else exhaustDirs' fs newfmt)

goLeftmost :: (Eq a) => FocusedMultiTree a -> Maybe (FocusedMultiTree a)
goLeftmost = exhaustDir goLeft

goRightmost :: (Eq a) => FocusedMultiTree a -> Maybe (FocusedMultiTree a)
goRightmost = exhaustDir goRight

goTop :: (Eq a) => FocusedMultiTree a -> Maybe (FocusedMultiTree a)
goTop = exhaustDir goUp

goBottomleft :: (Eq a) => FocusedMultiTree a -> Maybe (FocusedMultiTree a)
goBottomleft = exhaustDir (goDown 0)

goBottomright :: (Eq a) => FocusedMultiTree a -> Maybe (FocusedMultiTree a)
goBottomright = exhaustDirs [goDown 0, goRightmost]

goRight :: FocusedMultiTree a -> Maybe (FocusedMultiTree a)
goRight (FMT (t, cs)) = do
    (Cxt label lefts rights) <- safeHead cs
    focus <- safeHead $ rights
    return $ FMT (focus, (Cxt label (t:lefts) (tail rights)):(tail cs))

composeM :: (Monad m) => [a -> m a] -> a -> m a
composeM [] = return
composeM (f:fs) = f >=> composeM fs

doNav :: (Monad m) => FocusedMultiTree a -> [FocusedMultiTree a -> m (FocusedMultiTree a)] -> m (FocusedMultiTree a)
doNav = flip composeM

alterFocus :: (a -> a) -> FocusedMultiTree a -> FocusedMultiTree a
alterFocus f (FMT ((MT x ts), cs)) = FMT ((MT (f x) ts), cs)

replaceFocus :: a -> FocusedMultiTree a -> FocusedMultiTree a
replaceFocus x = alterFocus (\_ -> x)

removeFocus :: (Eq a) => FocusedMultiTree a -> MultiTree a
removeFocus fmt = fst $ extractFMT $ fromJust $ goTop fmt

-- Borrowed from Data.Tree source
drawTree :: MultiTree String -> String
drawTree  = unlines . draw

drawForest :: Forest String -> String
drawForest  = unlines . map drawTree

draw :: MultiTree String -> [String]
draw (MT x ts0) = x : drawSubTrees ts0
  where drawSubTrees [] = []
	drawSubTrees [t] =
		"|" : shift "`- " "   " (draw t)
	drawSubTrees (t:ts) =
		"|" : shift "+- " "|  " (draw t) ++ drawSubTrees ts

	shift first other = zipWith (++) (first : repeat other)

-- Test data

levels :: Int -> (Int, [Int])
levels n = (n, take n $ repeat (n-1))

countup :: Int -> (Int, [Int])
countup n = (n, [1..n-1])

statefulNumber :: a -> State Int (a, Int)
statefulNumber x = state $  \s -> ((x, s), s+1)

numberTree :: MultiTree a -> MultiTree (a, Int)
numberTree t = fst $ runState (mapM statefulNumber t) 0


testTree = unfoldTree countup 5
testTreef = focusedTree testTree

