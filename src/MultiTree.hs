module MultiTree where

import Control.Monad
import Data.Maybe 
import Control.Applicative

data MultiTree a = MT a (Forest a) deriving (Eq)

data Cxt a = Cxt { parentLabel :: a, lefts :: [MultiTree a], rights :: [MultiTree a] } deriving (Eq, Show)

type Context a = [Cxt a]
newtype FocusedMultiTree a = FMT { extractFMT :: (MultiTree a, Context a) } deriving (Eq)

class PrettyPrint a where
    pPrint :: a -> String

pPrintTabbed :: (Show a) => MultiTree a -> String
pPrintTabbed = pPrintTabbed' 0
    where pPrintTabbed' n (MT x ts) = replicate (2*n) ' ' ++ show x ++ "\n" ++ (concat $ map (pPrintTabbed' (n+1)) ts)

instance (Show a) => Show (FocusedMultiTree a) where
    show (FMT t) = show t

type Forest a = [MultiTree a]

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

instance (PrettyPrint a) => PrettyPrint (Maybe a) where
    pPrint Nothing = "Nothing!\n"
    pPrint (Just a) = pPrint a

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

testTree = unfoldTree countup 5
testTreef = focusedTree testTree

