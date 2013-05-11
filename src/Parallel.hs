module Parallel where
import MidIR
import Util
import qualified Data.Map as M
import ControlFlowGraph
import CFGConcrete
import CFGConstruct
import System.IO.Unsafe
import PrettyPrint
import Text.PrettyPrint.HughesPJ hiding (Str)
import Debug.Trace
import Control.Monad.State
import LowIR
import Data.IORef
import Data.Maybe
import Data.List
import Santiago
import Numeric.LinearProgramming

firefuel = "HI"

--parallelize::LGraph BranchingStatement Statement -> LGraph BranchingStatement Statement


treeParallelize midTree = unsafePerformIO $ do
		return $ evalState (stripper $ ddd midTree) []

parallelize midcfg = do
		midcfg --state
--		where (midcfg',state) = bleed midcfg earTag [] 
	

--Gather all BID's of for loops!
earTag bid scope p = do
		forloops<-get
	 	put $ newloop ++ forloops	
		return p
		where newloop 	| isPrefixOf ".for_test_" (getStr bid) = [bid] 
			  	| otherwise = [bid]


stripper (Prg code) = do
	code' <-  mapM fornicake code
	return $ Prg code'
{--		
indians l stmt 	
        | DFun name params bod		<- stmt = concatMap indians bod'
        | If expression thens elses 	<- stmt = concatMap indians thens ++ concapMap indians elses
        | While cond bod		<- stmt = concatMap indians bod
        | ForLoop i end bod		<- stmt = [i] ++ concatMap bod 
	| otherwise 				= [] 
--}

fornicake stmt 	
        | DFun name params bod		<- stmt = do
				bod' <- mapM fornicake bod
				return $ DFun name params bod'
        | If expression thens elses 	<- stmt = do
				thens' <- mapM fornicake thens
				elses' <- mapM fornicake elses
				return $ If expression thens' elses'
        | While cond bod		<- stmt = do
				bod' <- mapM fornicake bod
				return $ While cond bod'
        | ForLoop i end bod		<- stmt = do
				st<-get
				ret<- return $evalState (fortress stmt) st
				return ret
	| otherwise 				= do 
				return stmt

fortress for@(ForLoop i end bod) = do 
	bod' <- mapM fornicake bod
	vars<-get
--	is <- return $ indians for
	
	return $ Debug.Trace.traceShow i $ ForLoop i end bod'
{-

induct for@(ForLoop i end bod) = do
	vars<-get 
	is Inductive vars
	put $ transductions
        


-- adjust for indirectly inductive vars!


isInductive is expr
	| (Constant _) <- expr	= False
	| (Str 	    _) <- expr	= False
	| (Loc v)      <- expr  = elem v is
	| isInductive i (x expr)= True
	| isInductive i (y expr)= True
	| otherwise		= False







hemorhage g@(LGraph entryId blocks) l i  = (LGraph entryId outmap , state)
        where
          (outmap,state) = hemorhage' i [] ["global"] blocks  (fj $ M.lookup (lgEntry g) blocks) l

packageContent (ZLast (LastOther x)) = (x,[])
packageContent (ZLast _) = (None,[])
packageContent (ZTail instruction nextZTail) = (last, (instruction:xs))
	where (last,xs) = packageContent nextZTail

--bleed':: [BlockId] -> BlockLookup ProtoASM ProtoBranch-> Block ProtoASM ProtoBranch -> (BlockId ->[ProtoASM] -> [ProtoASM]) -> BlockLookup ProtoASM ProtoBranch
hemorhage' prestate visited scope g blk l = (M.insert bid newblock g' ,stateout)
                where
                        newblock = Block bid $ newZtail content newlast' 
					where newlast' = case newlast of
							None -> LastExit
							x    -> LastOther x
                        ((content,newlast),newstate) =  let pkg=packageContent $ bTail blk
				in  runState (l bid scope pkg ) prestate
                        bid = bId blk
                        last = getZLast blk
			lastinstr = case last of
				LastOther x -> x
				otherwise   -> None  
                                        --g':: BlockLookup ProtoASM ProtoBranch
                        (g',stateout) = case last of
                                (LastOther (WhileBranch _ b1 b2)) -> let
                                        stop' = endLabel b1
                                        blk1 = getblk b1 g
                                        blk2 = getblk b2 g
                                        bid2 = bId blk2
                                        bid1 = bId blk1
                                        (leftg ,state') = if unvisited b1
                                                then hemorhage' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l
                                                else (g,newstate)
                                        (rightg, state'') = if unvisited b2
                                                then hemorhage' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
                                                else (leftg,state')
                                        in if unvisited (BID stop')
                                                then hemorhage' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
                                                else (rightg,state'')


                                (LastOther (ForBranch _ _ b1 b2)) -> let
                                        stop' = endLabel b1
                                        blk1 = getblk b1 g
                                        blk2 = getblk b2 g
                                        bid2 = bId blk2
                                        bid1 = bId blk1
                                        (leftg ,state') = if unvisited b1
                                                then hemorhage' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l
                                                else (g,newstate)
                                        (rightg, state'') = if unvisited b2
                                                then hemorhage' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
                                                else (leftg,state')
                                        in if unvisited (BID stop')
                                                then hemorhage' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
                                                else (rightg,state'')


                                (LastOther (IfBranch _ b1 b2)) -> let
                                        stop' = endLabel b1
                                        blk1 = getblk b1 g
                                        blk2 = getblk b2 g
                                        bid2 = bId blk2
                                        bid1 = bId blk1
                                        (leftg,state') = if unvisited b1
                                                then hemorhage' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l
		                                 else (g,newstate)
                                        (rightg,state'') = if unvisited b2
                                                then hemorhage' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
                                                else (leftg, state')
                                        in if unvisited (BID stop')
                                                then hemorhage' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
                                                else (rightg,state'')


                                (LastOther (Jump b)) -> if unvisited b
                                                then  hemorhage' newstate (bid:visited) scope g (getblk b g) l
                                                else (g,newstate)
                                (LastOther (InitialBranch bs)) -> let cruz stt elm = hemorhage' (snd stt) ((bId $getblk elm $fst stt):bid:visited) ((getStr elm):scope)(fst stt) (getblk elm (fst stt)) l
                                        in skewer (g,newstate) cruz bs
                                _ -> (g,newstate)
                        unvisited id = not $ elem id visited
                        getblk b g = fromJust $ M.lookup b g
                        skewer st f (x:lst) = skewer st' f       lst
                                        where st' = if unvisited x
                                                then f st x
                                                else st
                        skewer st f [] = st


bleed g@(LGraph entryId blocks) l i  = (LGraph entryId outmap , state)
        where
          (outmap,state) = bleed' i [] ["global"] blocks  (fj $ M.lookup (lgEntry g) blocks) l

--bleed':: [BlockId] -> BlockLookup ProtoASM ProtoBranch-> Block ProtoASM ProtoBranch -> (BlockId ->[ProtoASM] -> [ProtoASM]) -> BlockLookup ProtoASM ProtoBranch
bleed' prestate visited scope g blk l = (M.insert bid newblock g' ,stateout)
                where
                        newblock = Block bid $ newZtail content last
                        (content,newstate) =  runState (l bid scope $  gatherContent $ bTail blk) prestate
                        bid = bId blk
                        last = getZLast blk
                                        --g':: BlockLookup ProtoASM ProtoBranch
                        (g',stateout) = case last of
                                (LastOther (WhileBranch _ b1 b2)) -> let
                                        stop' = endLabel b1
                                        blk1 = getblk b1 g
                                        blk2 = getblk b2 g
                                        bid2 = bId blk2
                                        bid1 = bId blk1
                                        (leftg ,state') = if unvisited b1
                                                then bleed' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l
                                                else (g,newstate)
                                        (rightg, state'') = if unvisited b2
                                                then bleed' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
                                                else (leftg,state')
                                        in if unvisited (BID stop')
                                                then bleed' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
                                                else (rightg,state'')
				(LastOther (ForBranch _ _ b1 b2)) -> let
                                        stop' = endLabel b1
                                        blk1 = getblk b1 g
                                        blk2 = getblk b2 g
                                        bid2 = bId blk2
                                        bid1 = bId blk1
                                        (leftg ,state') = if unvisited b1
                                                then bleed' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l
                                                else (g,newstate)
                                        (rightg, state'') = if unvisited b2
                                                then bleed' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
                                                else (leftg,state')
                                        in if unvisited (BID stop')
                                                then bleed' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
                                                else (rightg,state'')



                                (LastOther (IfBranch _ b1 b2)) -> let
                                        stop' = endLabel b1
                                        blk1 = getblk b1 g
                                        blk2 = getblk b2 g
                                        bid2 = bId blk2
                                        bid1 = bId blk1
                                        (leftg,state') = if unvisited b1
                                                then bleed' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l
		                                 else (g,newstate)
                                        (rightg,state'') = if unvisited b2
                                                then bleed' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
                                                else (leftg, state')
                                        in if unvisited (BID stop')
                                                then bleed' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
                                                else (rightg,state'')


                                (LastOther (Jump b)) -> if unvisited b
                                                then  bleed' newstate (bid:visited) scope g (getblk b g) l
                                                else (g,newstate)
                                (LastOther (InitialBranch bs)) -> let cruz stt elm = bleed' (snd stt) ((bId $getblk elm $fst stt):bid:visited) ((getStr elm):scope)(fst stt) (getblk elm (fst stt)) l
                                        in skewer (g,newstate) cruz bs
                                _ -> (g,newstate)
                        unvisited id = not $ elem id visited
                        getblk b g = fromJust $ M.lookup b g
                        skewer st f (x:lst) = skewer st' f       lst
                                        where st' = if unvisited x
                                                then f st x
                                                else st
                        skewer st f [] = st


solveLinearInteger x y z 
	| z == 0 = 0
	| y == 0 = 0
	| otherwise = 	let v = solveLinearInteger y (mod x y) (mod z y)
		       	in solveForX x y z v

solveForX x y z v = (-z -(y*v)) / x

getGCD x y = gcd x y
createPattern fi si 
	| any (\(x,y) -> x == y ) $ zip fi si = []
	| il > 2 = []
	|  otherwise =
	where 	
	--	any $ map (\(x,y) -> x/=y)
		il = length ilookup
		ilookup = filter (\(x,y,z) -> elem 0 [y,z]) zip3 [1..] fi si
		numvars = (min (length fi) (length si)) -1 
		
	
--}
	
