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
		return $ evalState (stripper midTree) []

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

indians stmt 	
        | DFun name params bod		<- stmt = concatMap indians bod
        | If expression thens elses 	<- stmt = concatMap indians thens ++ concatMap indians elses
        | While cond bod		<- stmt = concatMap indians bod
        | ForLoop i end bod		<- stmt = [i] ++ concatMap indians bod 
	| otherwise 				= [] 

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

drip sl el stmt
        | DFun name params bod		<- stmt = do
				bod' <- mapM (drip sl el) bod
				sl $DFun name params bod'
        | If expression thens elses 	<- stmt = do
				thens' <- mapM (drip sl el) thens
				elses' <- mapM (drip sl el) elses
				expr'  <- el expression
				sl $ If expr' thens' elses'
        | While cond bod		<- stmt = do
				bod' <- mapM (drip sl el) bod
				sl $While cond bod'
        | ForLoop i end bod		<- stmt = do	
				bod' <- mapM (drip sl el) bod
				sl $ForLoop i end bod'
        | otherwise 				= do 
				sl stmt


fortress for@(ForLoop i end bod) = do 
	bod' <- mapM fornicake bod
	vars<-get
	is <- return $ execState (drip induct (return) for) []
	ars <- return $ execState (drip (extractArrs) (return) for) []
	risky <-return $ nub $ filter (isInductive is) ars
	if parallelizable is risky
		then return $ ParaFor i end $ Debug.Trace.traceShow risky bod'
		else return $ ForLoop i end $ Debug.Trace.traceShow risky bod'

induct for@(ForLoop i end bod) = do
	vars<-get 
	put $ vars ++ [i]
	return for
induct x = do
	return x

-- make sure not to parallelize loops with returns
-- adjust for indirectly inductive vars!
data Access = Write {var::Variable} | Read {var::Variable} deriving (Show,Eq)
extractArrs stmt 
	| Set var expr <- stmt = do 
		vars <- get
		put $ vars ++ [Write var] ++  extractExprArrs expr 
		return stmt
	| Return expr <- stmt = do
 		vars <- get
		put $ vars ++  extractExprArrs expr 
		return stmt
	| Callout _ exprs <- stmt = do
		vars <- get
		put $ vars ++ concatMap extractExprArrs exprs	
		return stmt
	| Function _ exprs <- stmt = do
		vars <- get
		put $ vars ++ concatMap extractExprArrs exprs	
		return stmt
	| If expr _ _ <- stmt = do 
		vars <- get
		put $ vars ++  extractExprArrs expr	
		return stmt
		
	| While expr _ <- stmt = do 
		vars <- get
		put $ vars ++ extractExprArrs expr	
		return stmt
	
	| ForLoop  _ expr _ <- stmt = do 
		vars <- get
		put $ vars ++ extractExprArrs expr	
		return stmt
	
	| otherwise = do
		return stmt

extractExprArrs  expr
	| (Const _) <- expr	= []
	| (Str 	    _) <- expr	= []
	| (Loc  v@(Varray _ _)) <- expr  = [Read v]
	| (Loc v)      <- expr  = []
	| otherwise		= (extractExprArrs $ x expr)++(extractExprArrs $ y expr)

exprVars:: Expression -> [Variable]
exprVars  expr
	| (Const _) <- expr	= []
	| (Str 	    _) <- expr	= []
	| (Loc  v@(Var _)) <- expr  = [v]
	| (Loc v)      <- expr  = []
	| otherwise		= (exprVars $ x expr)++(exprVars $ y expr)



isInductive:: [Variable] -> Access -> Bool 
isInductive is ax
	| (Varray _ x)       <- Parallel.var ax  = any  (\x -> elem x is) $ exprVars x
	| otherwise		= False



parallelizable i b = False









{-

hemorhage g@(LGraph entryId blocks) l i  = (LGraph entryId outmap , state)
        where
          (outmap,state) = hemorhage' i [] ["global"] blocks  (fj $ M.lookup (lgEntry g) blocks) l

packageContent (ZLast (LastOther x)) = (x,[])
packageContent (ZLast _) = (None,[])
packageContent (ZTail instruction nextZTail) = (last, (instruction:xs))
	where (last,xs) = packageContent nextZTail
--bleed':: [BlockId] -> BlockLookup ProtoASM ProtoBranch-> Block ProtoASM ProtoBranch -> (BlockId ->[ProtoASM] -> [ProtoASM]) -> BlockLookup ProtoASM ProtoBranch
hemorhage' stop prestate visited scope g blk l = if (BID stop) == bid
			then (g,prestate)
			else (M.insert bid newblock g' ,stateout)
                where
                        newblock = Block bid $ newZtail content newlast' 
                        (content,newlast) =  let pkg= ratherContent $ bTail blk
				in  runState (l bid scope pkg ) prestate
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
					sc' bid2scope b1
                                        (leftg ,state') = if unvisited b1
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) (sc':scope) g blk1 l
                                                else (g,newstate) 
                                        (rightg, state'') = if unvisited b2
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
                                                else (leftg,newstate)
                                        in if unvisited (BID stop')
                                                then hemorhage' stop' newstate (((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
                                                else (rightg,newstate)


                                (LastOther (ForBranch _ _ b1 b2)) -> let
                                        stop' = endLabel b1
                                        blk1 = getblk b1 g
                                        blk2 = getblk b2 g
                                        bid2 = bId blk2
                                        bid1 = bId blk1
                                        (leftg ,state') = if unvisited b1
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l
                                                else (g,newstate)
                                        (rightg, state'') = if unvisited b2
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
                                                else (leftg,newstate)
                                        in if unvisited (BID stop')
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
                                                else (rightg,newstate)


                                (LastOther (IfBranch _ b1 b2)) -> let
                                        stop' = endLabel b1
                                        blk1 = getblk b1 g
                                        blk2 = getblk b2 g
                                        bid2 = bId blk2
                                        bid1 = bId blk1
                                        (leftg,state') = if unvisited b1
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope g blk1 l
		                                 else (g,newstate)
                                        (rightg,state'') = if unvisited b2
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope leftg blk2 l
                                                else (leftg, state')
                                        in if unvisited (BID stop')
                                                then hemorhage' stop' newstate ((BID stop'):bid2:bid1:bid:visited) scope rightg (getblk (BID stop') g) l
                                                else (rightg,newstate)


                                (LastOther (Jump b)) -> if unvisited b
                                                then  hemorhage' stop newstate (bid:visited) scope g (getblk b g) l
                                                else (g,newstate)
                                (LastOther (InitialBranch bs)) -> let cruz stt elm = hemorhage' stop (snd stt) ((bId $getblk elm $fst stt):bid:visited) ((getStr elm):scope)(fst stt) (getblk elm (fst stt)) l
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
		any $ map (\(x,y) -> x/=y)
		il = length ilookup
		ilookup = filter (\(x,y,z) -> elem 0 [y,z]) zip3 [1..] fi si
		numvars = (min (length fi) (length si)) -1 
		
	
--}
	
