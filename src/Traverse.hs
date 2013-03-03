module Traverse where

import Data.Maybe
import Prelude
import Transforms
import MultiTree
import Main
import qualified Data.IORef 
import qualified Data.HashMap.Strict as H
import System.IO.Unsafe
import Control.Monad.State
--data Node = Tree Node Node | Leaf  Int deriving (Show)

--expand:: STNode -> [Node]
-- GLOBALS
r = Data.IORef.readIORef
(<:)= Data.IORef.writeIORef
m = Data.IORef.modifyIORef
n = Data.IORef.newIORef
my = unsafePerformIO . n


-- #########GLOBALS##############
st = my H.empty
-- ##############################
expand (MT _ a) = a
expand _ = [] 

checkprepare f = convert.fromRight$testParse f 

arrDecCheck (MT (FD (Array n) _) [])  = Just $ n> 0   
arrDecCheck  _ = Nothing
checkArrayDeclarationNotZero p = traverse arrDecCheck p

mainMethod (MT (MD (_,"main")) _) = Just False 
mainMethod _ = Nothing
checkMainMethodDeclared p =  not (traverse mainMethod p)


breakContinue  (MT Break []) = Just False
breakContinue  (MT Continue []) = Just False
breakContinue  (MT (For _) _ ) = Just True;
breakContinue  (MT While _ ) = Just True;
breakContinue  _ = Nothing 
checkBreakContinue p = traverse breakContinue p

-- If the lambda returns nothing, expands the node and recurses. 
-- Checks that all the nodes that the lambda returns a value for
-- are true.

--traverse:: (Node-> Maybe Bool) -> Node -> Bool
traverse f tree = case (f tree) of 
		Just b -> b
		Nothing -> and $ map (traverse f) (expand tree)
{--

x = (Tree (Tree (Tree (Leaf 4) (Leaf 2) )( Lea f 5))( Leaf 5))




--treeMapReduce:: (Node -> Maybe [a]) -> ([a] -> [a] -> [a]) -> Node -> [a] 
--}
scrapeFDs  (MT fd@(FD _ _) _ ) = Just fd
scrapeFDs _ = Nothing

data SymbolContext = SymbolContext String 

collectFDs a (MT n b) = (MT n (a ++ b))
	
treeMapReduce apply merge tree = case (apply tree) of 
		Just val -> foldr merge [] [val]
		Nothing -> foldr merge [] (map (treeMapReduce apply merge) (expand tree))

scrapeBlocks (MT DBlock children) = Just children
scrapeBlocks (MT Prog children) = Just children
scrapeBlocks _ = Nothing

data SymbolTable = SymbolTable String SymbolTable [STNode]| Empty
	deriving (Show)

nextBlocks p = if not $ null blocks 
			then nextBl
	where 	children = expand p
		blocks   = map fromJust $ filter isJust $ map scrapeBlocks $children	
fdsCollect p = map fromJust $filter isJust $map scrapeFDs $expand p
	
