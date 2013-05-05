module Santiago where

import CFGConstruct
import CFGConcrete
import System.IO.Unsafe
import Control.Monad.State
import LowIR
import Data.Maybe
import Data.List
import Debug.Trace

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

fj x = fromJust $ case x of
	Nothing -> Debug.Trace.traceShow x Nothing
	x ->x

cruise g@(LGraph entryId blocks) l = LGraph entryId $ cruise' [] blocks  (fj $ M.lookup (lgEntry g) blocks) l 

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
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					leftg = if unvisited b1 
						then cruise' (bid:visited) g blk1 l 
						else g
					in if unvisited b2
						then cruise' (bid:visited) leftg blk2 l
						else leftg
				(LastOther (If' _ (b1:b2:_))) -> let 
					blk1 = getblk b1 g 
					blk2 = getblk b2 g 
					leftg = if unvisited b1 
						then cruise' (bid:visited) g blk1 l 
						else g
					in if unvisited b2
						then cruise' (bid:visited) leftg blk2 l
						else leftg
				(LastOther (Jump' b)) -> cruise' (bid:visited) g (getblk b g) l 
				(LastOther (InitialBranch' bs)) -> let cruz stt elm = cruise' (bid:visited) stt (getblk elm stt) l 
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
	  (outmap,state) = kruise' i [] ["global"] blocks  (fj $ M.lookup (lgEntry g) blocks) l


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
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					(leftg ,state') = if unvisited b1 
						then kruise' newstate (bid:visited) scope g blk1 l 
						else (g,newstate)
					in if unvisited b2
						then kruise' state' (bid:visited) scope leftg blk2 l
						else (leftg,state')
				(LastOther (If' _ (b1:b2:_))) -> let 
					blk1 = getblk b1 g 
					blk2 = getblk b2 g 
					(leftg,state') = if unvisited b1 
						then kruise' newstate (bid:visited) scope g blk1 l 
						else (g,newstate)
					in if unvisited b2
						then kruise' state' (bid:visited) scope leftg blk2 l
						else (leftg, state')
				(LastOther (Jump' b)) -> kruise' newstate (bid:visited) scope g (getblk b g) l 
				(LastOther (InitialBranch' bs)) -> let cruz stt elm = kruise' (snd stt) (bid:visited) ((getStr elm):scope)(fst stt) (getblk elm (fst stt)) l 
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
	  (outmap,state) = trickle' "" i [] ["global"] blocks  (fj $ start) l
          start = case M.lookup (lgEntry g) blocks of
		Nothing -> Debug.Trace.trace "FIRE!" Nothing
		x	-> x






trickle' stop prestate visited scope g blk l = if (BID stop) == bid 
				then (g,prestate)
				else (M.insert bid (newblock)  g' ,stateout)
		where 
			newblock = Block bid $ newZtail content last
			(content,newstate) = runState (l bid scope $ gatherContent $ bTail blk) prestate
			bid = bId blk
			last = getZLast blk
					--g':: BlockLookup ProtoASM ProtoBranch
			(g', stateout) = case last of  
				(LastOther (While' _ (b1:b2:_))) -> let
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g
					sc' = bid2scope b1
					(leftg ,state') = if unvisited b1 
						then trickle' stop' newstate (bid:visited) (sc':scope) g blk1 l 
						else (g,newstate)
					(rightg,state'') = if unvisited b2
						then trickle' stop' newstate (bid:visited) (sc':scope) leftg blk2 l
						else (leftg,newstate)
					in if unvisited (BID stop')
						then trickle' stop newstate (bid:visited) scope rightg (getblk (BID stop') g) l
						else (leftg,newstate)
				(LastOther (If' _ (b1:b2:_))) -> let 
					sc' = bid2scope b1
					stop' = endLabel b1
					blk1 = getblk b1 g 
					blk2 = getblk b2 g 
					(leftg,state') = if unvisited b1 
						then trickle' stop' newstate (bid:visited) (sc':scope) g blk1 l 
						else (g,newstate)
					(rightg,state'') = if unvisited b2
						then trickle' stop' newstate (bid:visited) (sc':scope) leftg blk2 l
						else (leftg, newstate)
					in if unvisited (BID stop')
						then trickle' stop newstate (bid:visited) scope rightg (getblk (BID stop') g) l
						else (leftg,newstate)
				(LastOther (Jump' b)) -> if b /= (BID stop) 
					then trickle' stop newstate (bid:visited) scope g (getblk b g) l 
					else (g,newstate)
				(LastOther (InitialBranch' bs)) -> let cruz stt elm = trickle' stop (snd stt) (bid:visited) ((getStr elm):scope) (fst stt) (getblk elm (fst stt)) l 
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
		| isPrefixOf ".if_true_" str = "if" ++  drop 8 str
		| isPrefixOf ".if_false_" str = "if" ++  drop 9 str
		| isPrefixOf ".loop_body_" str = "loop" ++  drop 10 str
		| isPrefixOf ".loop_test_" str = "loop" ++  drop 10 str
		| isPrefixOf ".loop_end_" str = "loop" ++  drop 9 str
	

endLabel bid = endlabel name  
      where
	name = getStr bid
	endlabel str  
		| isPrefixOf ".if_true_" str = ".endif_" ++  drop 9 str
		| isPrefixOf ".if_false_" str = ".endif_" ++  drop 10 str
		| isPrefixOf ".loop_body_" str = ".loop_end_" ++  drop 11 str
		| isPrefixOf ".loop_test_" str = ".loop_end_" ++  drop 11 str
		| isPrefixOf ".loop_end_" str = ".loop_end_" ++  drop 10 str



