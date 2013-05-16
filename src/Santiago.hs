module Santiago where

import CFGConstruct
import CFGConcrete
import System.IO.Unsafe
import Control.Monad.State
import LowIR
import Data.Maybe
import Data.List
import Debug.Trace
import MidIR
import ControlFlowGraph
import qualified Data.Map as M
-- cfg is ugly. I fix. fo goood woking compirar !!!! hao hao hao-er zuo gong ke ye zuo dou dian nau wen ti!!!

fmapGraph asmLambda branchLambda (LGraph entryId blocks) = LGraph entryId blocks'
	where blocks' = M.map (fmapBlock (asmLambda) (branchLambda)) blocks

fmapBlock al bl (Block bid ztail) = Block bid newZtail'
		where 
			((preMids,endMids), newlast) =  bl bid $ getZLast ztail 
			newZtail' = newZtail newMiddles newlast
			mappedMiddles = concatMap  (al bid) $ gatherContent ztail
			newMiddles =  (preMids ++ mappedMiddles ++ endMids) 

newZtail [] zl = ZLast zl
newZtail (m:ms) zl = ZTail m (newZtail ms zl)

-- ZTail -> [asm]
gatherContent (ZLast _) = []
gatherContent (ZTail instruction nextZTail) = instruction : gatherContent nextZTail

--pulls out expressions from the protobranches cuz they make code annoying!
--degut

fj i x = fromJust $ case x of
	Nothing -> Debug.Trace.trace ((show i) ++ (show x)) Nothing
	x ->x

ddd x = Debug.Trace.traceShow x x

insertListMap ((x,y):xs) mp = M.insert x y (insertListMap xs mp)
insertListMap [] mp = mp


cruise g@(LGraph entryId blocks) l = LGraph entryId $ cruise' [] blocks  (fj 1 $ M.lookup (lgEntry g) blocks) l 

cruise':: [BlockId] -> BlockLookup ProtoASM ProtoBranch-> Block ProtoASM ProtoBranch -> (BlockId ->[ProtoASM] -> [ProtoASM]) -> BlockLookup ProtoASM ProtoBranch
cruise' visited g blk l =M.insert bid newblock g' 
		where 
			bid = bId blk
			newblock = Block bid $ newZtail content last
			content = l bid $gatherContent $ bTail blk
			last = getZLast blk
			g':: BlockLookup ProtoASM ProtoBranch
			g' = case last of  
				(LastOther (While' _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					bid2 = bId blk2
					bid1 = bId blk1
					leftg = if unvisited b1 
						then cruise' ((BID stop'):bid2:bid1:visited) g blk1 l 
						else g
					rightg = if unvisited b2
						then cruise' ((BID stop'):bid2:bid1:visited) leftg blk2 l
						else leftg
					in if unvisited (BID stop')
						then cruise' ((BID stop'):bid2:bid1:bid:visited) rightg (getblk (BID stop') g) l
						else rightg
				(LastOther (For' _ _ _ _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					bid2 = bId blk2
					bid1 = bId blk1
					leftg = if unvisited b1 
						then cruise' ((BID stop'):bid2:bid1:visited) g blk1 l 
						else g
					rightg = if unvisited b2
						then cruise' ((BID stop'):bid2:bid1:visited) leftg blk2 l
						else leftg
					in if unvisited (BID stop')
						then cruise' ((BID stop'):bid2:bid1:bid:visited) rightg (getblk (BID stop') g) l
						else rightg
				(LastOther (Parafor' _ _ _ _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					bid2 = bId blk2
					bid1 = bId blk1
					leftg = if unvisited b1 
						then cruise' ((BID stop'):bid2:bid1:visited) g blk1 l 
						else g
					rightg = if unvisited b2
						then cruise' ((BID stop'):bid2:bid1:visited) leftg blk2 l
						else leftg
					in if unvisited (BID stop')
						then cruise' ((BID stop'):bid2:bid1:bid:visited) rightg (getblk (BID stop') g) l
						else rightg
			
				(LastOther (If' _ (b1:b2:_))) -> let 
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g 
					bid1 = bId blk1
					bid2 = bId blk2
					leftg = if unvisited b1 
						then cruise' ((BID stop'):bid2:bid1:bid:visited) g blk1 l 
						else g
					rightg = if unvisited b2
						then cruise' ((BID stop'):bid2:bid1:bid:visited) leftg blk2 l
						else leftg
					in if unvisited (BID stop')
						then cruise' ((BID stop'):bid2:bid1:bid:visited) rightg (getblk (BID stop') g) l
						else rightg
	

				(LastOther (Jump' b)) -> if unvisited b 
						then cruise' (bid:visited) g (getblk b g) l 
						else g
				(LastOther (InitialBranch' bs)) -> let cruz stt elm = cruise' ((bId $getblk elm stt):bid:visited) stt (getblk elm stt) l 
					in skewer g cruz bs
				_ -> g
			functions = concatMap getDfun content
			getDfun (DFun' name _) = [BID name]
			getDfun _ = [] 
			unvisited id = not $ elem id visited
			getblk b g = fromJust $ M.lookup b g 
			skewer st f (x:lst) = skewer st' f	 lst
					where st' = if unvisited x 
						then f st x
						else st
			skewer st f [] = st

kruise g@(LGraph entryId blocks) l i  = (LGraph entryId outmap , state)
	where 
	  (outmap,state) = kruise' i [] ["global"] blocks  (fj 7 $ M.lookup (lgEntry g) blocks) l


--kruise':: [BlockId] -> BlockLookup ProtoASM ProtoBranch-> Block ProtoASM ProtoBranch -> (BlockId ->[ProtoASM] -> [ProtoASM]) -> BlockLookup ProtoASM ProtoBranch
kruise' prestate visited scope g blk l = (M.insert bid newblock g' ,stateout)
		where 
			newblock = Block bid $ newZtail content last
			(content,newstate) =  runState (l bid scope $ gatherContent $ bTail blk) prestate
			bid = bId blk
			last = getZLast blk
					--g':: BlockLookup ProtoASM ProtoBranch
			(g',stateout) = case last of  
				(LastOther (While' _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					bid2 = bId blk2
					bid1 = bId blk1
					(leftg ,state') = if unvisited b1 
						then kruise' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l 
						else (g,newstate)
					(rightg, state'') = if unvisited b2
						then kruise' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
						else (leftg,state')
					in if unvisited (BID stop')
						then kruise' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,state'')
	
				(LastOther (For' _ _ _ _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					bid2 = bId blk2
					bid1 = bId blk1
					(leftg ,state') = if unvisited b1 
						then kruise' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l 
						else (g,newstate)
					(rightg, state'') = if unvisited b2
						then kruise' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
						else (leftg,state')
					in if unvisited (BID stop')
						then kruise' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,state'')
				(LastOther (Parafor' _ _ _ _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					bid2 = bId blk2
					bid1 = bId blk1
					(leftg ,state') = if unvisited b1 
						then kruise' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l 
						else (g,newstate)
					(rightg, state'') = if unvisited b2
						then kruise' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
						else (leftg,state')
					in if unvisited (BID stop')
						then kruise' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,state'')
	
				(LastOther (If' _ (b1:b2:_))) -> let 
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g 
					bid2 = bId blk2
					bid1 = bId blk1
					(leftg,state') = if unvisited b1 
						then kruise' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l 
						else (g,newstate)
					(rightg,state'') = if unvisited b2
						then kruise' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
						else (leftg, state')
					in if unvisited (BID stop')
						then kruise' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,state'')
	

				(LastOther (Jump' b)) -> if unvisited b
						then  kruise' newstate (bid:visited) scope g (getblk b g) l
						else (g,newstate)
				(LastOther (InitialBranch' bs)) -> let cruz stt elm = kruise' (snd stt) ((bId $getblk elm $fst stt):bid:visited) ((getStr elm):scope)(fst stt) (getblk elm (fst stt)) l 
					in skewer (g,newstate) cruz bs
				_ -> (g,newstate)
			unvisited id = not $ elem id visited
			getblk b g = fromJust $ M.lookup b g 
			skewer st f (x:lst) = skewer st' f	 lst
					where st' = if unvisited x 
						then f st x
						else st
			skewer st f [] = st


trickle g@(LGraph entryId blocks) l i  = (LGraph entryId outmap , state)
	where 
	  (outmap,state) = trickle' "" i [] ["global"] blocks  (fj 2 $ start) l
          start = case M.lookup (lgEntry g) blocks of
		Nothing -> Debug.Trace.trace "FIRE!" Nothing
		x	-> x






trickle' stop prestate visited scope g blk l = if (BID stop) == bid 
				then (g,prestate)
				else (M.insert bid (newblock)  g' ,stateout)
		where 
			newblock = Block bid $ newZtail content last
			(content,newstate) =  runState (l bid scope $ gatherContent $ bTail blk) prestate
			bid = bId blk
			last = getZLast blk
					--g':: BlockLookup ProtoASM ProtoBranch
			(g', stateout) = case last of  
				(LastOther (While' _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					bid2 = bId blk2
					bid1 = bId blk1
					sc' = bid2scope b1
					(leftg ,state') = if unvisited b1 
						then trickle' stop' newstate ((BID stop'):bid2:bid1:bid:visited) (sc':scope) g blk1 l 
						else (g,newstate)
					(rightg,state'') = if unvisited b2
						then trickle' stop' newstate ((BID stop'):bid2:bid1:bid:visited) (sc':scope) leftg blk2 l
						else (leftg,newstate)
					in if unvisited (BID stop')
						then trickle' stop newstate ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,newstate)
				(LastOther (For' _ _ _ _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					bid2 = bId blk2
					bid1 = bId blk1
					sc' = bid2scope b1
					(leftg ,state') = if unvisited b1 
						then trickle' stop' newstate ((BID stop'):bid2:bid1:bid:visited) (sc':scope) g blk1 l 
						else (g,newstate)
					(rightg,state'') = if unvisited b2
						then trickle' stop' newstate ((BID stop'):bid2:bid1:bid:visited) (sc':scope) leftg blk2 l
						else (leftg,newstate)
					in if unvisited (BID stop')
						then trickle' stop newstate ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,newstate)
	
				(LastOther (Parafor' _ _ _ _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					bid2 = bId blk2
					bid1 = bId blk1
					sc' = bid2scope b1
					(leftg ,state') = if unvisited b1 
						then trickle' stop' newstate ((BID stop'):bid2:bid1:bid:visited) (sc':scope) g blk1 l 
						else (g,newstate)
					(rightg,state'') = if unvisited b2
						then trickle' stop' newstate ((BID stop'):bid2:bid1:bid:visited) (sc':scope) leftg blk2 l
						else (leftg,newstate)
					in if unvisited (BID stop')
						then trickle' stop newstate ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,newstate)
	
				(LastOther (If' _ (b1:b2:_))) -> let 
					sc' = bid2scope b1
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g 
					bid2 = bId blk2
					bid1 = bId blk1
					(leftg,state') = if unvisited b1 
						then trickle' stop' newstate ((BID stop'):bid2:bid1:bid:visited) (sc':scope) g blk1 l 
						else (g,newstate)
					(rightg,state'') = if unvisited b2
						then trickle' stop' newstate ((BID stop'):bid2:bid1:bid:visited) (sc':scope) leftg blk2 l
						else (leftg, newstate)
					in if unvisited (BID stop')
						then trickle' stop newstate ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,newstate)
				(LastOther (Jump' b)) -> if b /= (BID stop) 
					then trickle' stop newstate (b:bid:visited) scope g (getblk b g) l 
					else (g,newstate)
				(LastOther (InitialBranch' bs)) -> let cruz stt elm = trickle' stop (snd stt) ((bId $getblk elm $fst stt):bid:visited) ((getStr elm):scope) (fst stt) (getblk elm (fst stt)) l 
					in skewer (g,newstate) cruz $ bs
				_ -> (g,newstate)
			unvisited id = not $ elem id visited
			getblk b g = fromJust $ M.lookup b g 
			skewer st f (x:lst) = skewer st' f	 lst
					where st' = if unvisited x 
						then f st x
						else st
			skewer st f [] = st

bid2scope bid = endlabel name  
      where
	name = getStr bid
	endlabel str  
		| isPrefixOf ".if_true" str = "if" ++  drop 7 str
		| isPrefixOf ".if_false" str = "if" ++  drop 8 str
		| isPrefixOf ".loop_body" str = "loop" ++  drop 9 str
		| isPrefixOf ".loop_test" str = "loop" ++  drop 9 str
		| isPrefixOf ".loop_end" str = "loop" ++  drop 8 str
		| isPrefixOf ".for_end" str = "for" ++  drop 7 str
		| isPrefixOf ".for_body" str = "for" ++  drop 8 str
		| isPrefixOf ".for_test" str = "for" ++  drop 8 str
		| isPrefixOf ".parafor_end" str = "parafor" ++  drop 11 str
		| isPrefixOf ".parafor_body" str = "parafor" ++  drop 12 str
		| isPrefixOf ".parafor_test" str = "parafor" ++  drop 12 str
	
testLabel bid = testlabel name  
      where
	name = getStr bid
	testlabel str  
		| isPrefixOf ".loop_body" str = ".loop_test" ++  drop 10 str
		| isPrefixOf ".loop_test" str = ".loop_test" ++  drop 10 str
		| isPrefixOf ".loop_end" str = ".loop_test" ++  drop 9 str


endLabel bid = endlabel name  
      where
	name = getStr bid
	endlabel str  
		| isPrefixOf ".if_true" str = ".endif" ++  drop 8 str
		| isPrefixOf ".if_false" str = ".endif" ++  drop 9 str
		| isPrefixOf ".loop_body" str = ".loop_end" ++  drop 10 str
		| isPrefixOf ".loop_test" str = ".loop_end" ++  drop 10 str
		| isPrefixOf ".loop_end" str = ".loop_end" ++  drop 9 str
		| isPrefixOf ".for_end" str = ".for_end" ++  drop 8 str
		| isPrefixOf ".for_body" str = ".for_end" ++  drop 9 str
		| isPrefixOf ".for_test" str = ".for_end" ++  drop 9 str
		| isPrefixOf ".parafor_end" str = ".parafor_end" ++  drop 12 str
		| isPrefixOf ".parafor_body" str = ".parafor_end" ++  drop 13 str
		| isPrefixOf ".parafor_test" str = ".parafor_end" ++  drop 13 str
		| otherwise = error $ name

trickleLast g@(LGraph entryId blocks) l i  = (LGraph entryId outmap , state)
	where 
	  (outmap,state) = trickleL' "" i [] ["global"] blocks  (fj 3 $ start) l
          start = case M.lookup (lgEntry g) blocks of
		Nothing -> Debug.Trace.trace "FIRE!" Nothing
		x	-> x



--- passes last to lambda
trickleL' stop prestate visited scope g blk l = if (BID stop) == bid 
				then (g,prestate)
				else (M.insert bid (newblock)  g' ,stateout)
		where 
			newblock = Block bid $ newZtail content last
			(content,newstate) =  runState (l (cl') bid scope $ gatherContent $ bTail blk) prestate
			bid = bId blk
			last = getZLast blk
			cl' = case last of
				(LastOther x )-> x
				_ -> Nil		 --bahh lazyness
					--g':: BlockLookup ProtoASM ProtoBranch
			(g', stateout) = case last of  
				(LastOther k@(While' _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					sc' = bid2scope b1
					(leftg ,state') = if unvisited b1 
						then trickleL' stop' newstate (bid:visited) (sc':scope) g blk1 l 
						else (g,newstate)
					(rightg,state'') = if unvisited b2
						then trickleL' stop' newstate (bid:visited) (sc':scope) leftg blk2 l
						else (leftg,newstate)
					in if unvisited (BID stop')
						then trickleL' stop newstate (bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,newstate)

				(LastOther k@(For' _ _ _ _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					sc' = bid2scope b1
					(leftg ,state') = if unvisited b1 
						then trickleL' stop' newstate (bid:visited) (sc':scope) g blk1 l 
						else (g,newstate)
					(rightg,state'') = if unvisited b2
						then trickleL' stop' newstate (bid:visited) (sc':scope) leftg blk2 l
						else (leftg,newstate)
					in if unvisited (BID stop')
						then trickleL' stop newstate (bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,newstate)
	
				(LastOther k@(Parafor' _ _ _ _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					sc' = bid2scope b1
					(leftg ,state') = if unvisited b1 
						then trickleL' stop' newstate (bid:visited) (sc':scope) g blk1 l 
						else (g,newstate)
					(rightg,state'') = if unvisited b2
						then trickleL' stop' newstate (bid:visited) (sc':scope) leftg blk2 l
						else (leftg,newstate)
					in if unvisited (BID stop')
						then trickleL' stop newstate (bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,newstate)
	

				(LastOther k@(If' _ (b1:b2:_))) -> let 
					sc' = bid2scope b1
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g 
					(leftg,state') = if unvisited b1 
						then trickleL' stop' newstate (bid:visited) (sc':scope) g blk1 l 
						else (g,newstate)
					(rightg,state'') = if unvisited b2
						then trickleL' stop' newstate (bid:visited) (sc':scope) leftg blk2 l
						else (leftg, newstate)
					in if unvisited (BID stop')
						then trickleL' stop newstate (bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,newstate)
				(LastOther k@(Jump' b)) -> if b /= (BID stop) 
					then trickleL' stop newstate (bid:visited) scope g (getblk b g) l 
					else (g,newstate)
				(LastOther k@(InitialBranch' bs)) -> let cruz stt elm = trickleL'  stop (snd stt) ((bId $getblk elm $fst stt):bid:visited) ((getStr elm):scope) (fst stt) (getblk elm (fst stt)) l 
					in skewer (g,newstate) cruz $ bs
				_ -> (g,newstate)
			unvisited id = not $ elem id visited
			getblk b g = fromJust $ M.lookup b g 
			skewer st f (x:lst) = skewer st' f	 lst
					where st' = if unvisited x 
						then f st x
						else st
			skewer st f [] = st


--- esiurk = reverse kruise ! Traverse State backwards! get it :-) ?

esiurk g@(LGraph entryId blocks) l i  = (LGraph entryId outmap , state)
	where 
	  (outmap,state) = esiurk' i [] ["global"] blocks  (fj 4 $ M.lookup (lgEntry g) blocks) l


--kruise':: [BlockId] -> BlockLookup ProtoASM ProtoBranch-> Block ProtoASM ProtoBranch -> (BlockId ->[ProtoASM] -> [ProtoASM]) -> BlockLookup ProtoASM ProtoBranch
esiurk' prestate visited scope g blk l = (M.insert bid newblock g' ,newstate)
		where 
			newblock = Block bid $ newZtail content last
			(content,newstate) =  runState (l bid scope $ gatherContent $ bTail blk) stateout
			bid = bId blk
			last = getZLast blk
					--g':: BlockLookup ProtoASM ProtoBranch
			(g',stateout) = case last of  
				(LastOther (While' _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b2 g 
					blk2 = getblk b1 g
					bid2 = bId blk2
					bid1 = bId blk1
					(leftg ,state') = if unvisited b1 
						then esiurk' prestate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l 
						else (g,prestate)
					(rightg, state'') = if unvisited b2
						then esiurk' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
						else (leftg,state')
					in if unvisited (BID stop')
						then esiurk' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,state'')
	
				(LastOther (For' _ _ _ _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b2 g 
					blk2 = getblk b1 g
					bid2 = bId blk2
					bid1 = bId blk1
					(leftg ,state') = if unvisited b1 
						then esiurk' prestate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l 
						else (g,prestate)
					(rightg, state'') = if unvisited b2
						then esiurk' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
						else (leftg,state')
					in if unvisited (BID stop')
						then esiurk' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,state'')
		
				(LastOther (Parafor' _ _ _ _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b2 g 
					blk2 = getblk b1 g
					bid2 = bId blk2
					bid1 = bId blk1
					(leftg ,state') = if unvisited b1 
						then esiurk' prestate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l 
						else (g,prestate)
					(rightg, state'') = if unvisited b2
						then esiurk' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
						else (leftg,state')
					in if unvisited (BID stop')
						then esiurk' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,state'')
	


				(LastOther (If' _ (b1:b2:_))) -> let 
					stop' = endLabel b1
					blk1 = getblk b2 g 
					blk2 = getblk b1 g 
					bid2 = bId blk2
					bid1 = bId blk1
					(leftg,state') = if unvisited b1 
						then esiurk' prestate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l 
						else (g,prestate)
					(rightg,state'') = if unvisited b2
						then esiurk' state' ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
						else (leftg, state')
					in if unvisited (BID stop')
						then esiurk' state' ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
						else (rightg,state'')
	

				(LastOther (Jump' b)) -> if unvisited b
						then  esiurk' prestate (bid:visited) scope g (getblk b g) l
						else (g,prestate)
				(LastOther (InitialBranch' bs)) -> let cruz stt elm = esiurk' (snd stt) ((bId $getblk elm $fst stt):bid:visited) ((getStr elm):scope)(fst stt) (getblk elm (fst stt)) l 
					in skewer (g,prestate) cruz bs
				_ -> (g,prestate)
			unvisited id = not $ elem id visited
			getblk b g = fromJust $ M.lookup b g 
			skewer st f (x:lst) = skewer st' f	 lst
					where st' = if unvisited x 
						then f st x
						else st
			skewer st f [] = st


-- fuck it Ill make it specific to scoping
hemorhage g@(LGraph entryId blocks) l ll i = (LGraph entryId outmap , state)
        where
          (outmap,state) = hemorhage' "" i [] ["global"] blocks  (fj 5$ M.lookup (lgEntry g) blocks) l ll

hemorhage' stop prestate visited scope g blk l ll= if (BID stop) == bid
                        then (g,prestate)
                        else (M.insert bid newblock g' ,prestate)
                where
                        newblock = Block bid $ newZtail content last
                        (content,newstate) =  let pkg= gatherContent $ bTail blk
                                in  runState (l bid scope pkg ) prestate
                        bid = bId blk
                        last = case getZLast blk of
					(LastOther x) 	-> LastOther $evalState (ll x scope) stateout	
					x 		-> x
                                        --g':: BlockLookup ProtoASM ProtoBranch
                        (g',stateout) = case last of
                                (LastOther (WhileBranch _ b1 b2)) -> let
                                        stop' = endLabel b1
                                        blk1 = getblk b1 g
                                        blk2 = getblk b2 g
                                        bid2 = bId blk2
                                        bid1 = bId blk1
                                        sc' = bid2scope b1
                                        (leftg ,state') = if unvisited b1
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) (sc':scope) g blk1 l ll
                                                else (g,newstate)
                                        (rightg, state'') = if unvisited b2
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l ll
                                                else (leftg,state')
                                        in if unvisited (BID stop')
                                                then hemorhage' stop newstate ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l ll
                                                else (rightg,state'')


                                (LastOther (ForBranch _ _ _ b1 b2)) -> let
                                        stop' = endLabel b1
                                        blk1 = getblk b1 g
                                        blk2 = getblk b2 g
                                        bid2 = bId blk2
                                        bid1 = bId blk1
                                        (leftg ,state') = if unvisited b1
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l ll
                                                else (g,newstate)
                                        (rightg, state'') = if unvisited b2
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l ll
                                                else (leftg,state')
                                        in if unvisited (BID stop')
                                                then hemorhage' stop newstate ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l ll
                                                else (rightg,state'')

				(LastOther (ParaforBranch _ _ _ b1 b2)) -> let
                                        stop' = endLabel b1
                                        blk1 = getblk b1 g
                                        blk2 = getblk b2 g
                                        bid2 = bId blk2
                                        bid1 = bId blk1
                                        (leftg ,state') = if unvisited b1
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l ll
                                                else (g,newstate)
                                        (rightg, state'') = if unvisited b2
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l ll
                                                else (leftg,state')
                                        in if unvisited (BID stop')
                                                then hemorhage' stop newstate ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l ll
                                                else (rightg,state'')



                                (LastOther (IfBranch _ b1 b2)) -> let
                                        stop' = endLabel b1
                                        blk1 = getblk b1 g
                                        blk2 = getblk b2 g
                                        bid2 = bId blk2
                                        bid1 = bId blk1
                                        (leftg,state') = if unvisited b1
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l ll
                                                 else (g,newstate)
                                        (rightg,state'') = if unvisited b2
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l ll
                                                else (leftg, state')
                                        in if unvisited (BID stop')
                                                then hemorhage' stop newstate ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l ll
                                                else (rightg,state'')


                                (LastOther (Jump b)) -> if unvisited b
                                                then  hemorhage' stop newstate (bid:visited) scope g (getblk b g) l ll
                                                else (g,newstate)
                                (LastOther (InitialBranch bs)) -> let cruz stt elm = hemorhage' stop (prestate) ((bId $getblk elm $fst stt):bid:visited) ((getStr elm):scope)(fst stt) (getblk elm (fst stt)) l ll
                                        in skewer (g,newstate) cruz bs
                                _ -> (g,newstate) 
                        unvisited id = not $ elem id visited
                        getblk b g = fromJust $ M.lookup b g
                        skewer st f (x:lst) = skewer st' f       lst
                                        where st' = if unvisited x
                                                then f st x
                                                else st
                        skewer st f [] = st

