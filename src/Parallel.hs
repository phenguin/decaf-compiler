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
import Control.Monad.State
import Data.List
import Santiago
import Numeric.LinearProgramming
import qualified Data.Map as M

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


snoper prg = evalState (snipe prg)  ([Global] , M.empty ,0)

snipe (Prg code) = do
	code' <- mapM forn code-- ([Global] , M.empty ,0)
	return$ Prg code'

fornbod bd = mapM forn bd



--forn:: State ([Scoped], (M.Map Variable [Scoped]) , Int) m => Statement -> m Statement
forn stmt 	
        | DFun name params bod		<- stmt = do
				st'@(scp, mp,i) <- get
				st <- return $ ((scp++[Func name]),mp,i+1)
				put $ (scp, mp ,i+1)
				return $ DFun name  [] (evalState (fornbod ((map (DVar) params) ++bod)) st )
        | If expression thens elses 	<- stmt = do
				st'@(scp , mp,i) <- get
				st <- return $((scp++[Loop (show i)]),mp,i+1)
				put $ (scp, mp ,i+1)
				exp' <- fornex expression
				return $ If (exp') (evalState (fornbod thens) st) (evalState (fornbod elses) st)
        | While cond bod		<- stmt = do
				st'@(scp, mp,i) <- get
				st <- return $((scp++[Loop (show i)]),mp,i+1)
				put $ (scp, mp ,i+1)
				cond' <- fornex cond
				return $ While (cond') (evalState (fornbod bod) st) 
        | ForLoop v start end bod 	<- stmt = do
				st'@(scp, mp,i) <- get
				st <- return $((scp++[Loop (show i)]),mp,i+1)
				put $ (scp, mp ,i+1)
				i' <- fornvar v 
				start' <- fornex start
				end' <- fornex end
				return $ ForLoop i' start' end' (evalState (fornbod bod) st) 
	| DVar x <- stmt = do
		st@(scp,mp,i)<-get
		put $(scp,(M.insert x scp mp),i)
		x'<-fornvar x 
		return $ DVar x'
	| Set var expr <- stmt = do 
		var'<- fornvar var
		expr' <- fornex expr
		return $ (Set var' expr')
	| Return expr <- stmt = do
		expr' <- fornex expr
		return $ Return expr' 
	| Callout f exprs <- stmt = do
		exprs' <- mapM fornex exprs
		return $ Callout f exprs'
	| Function f exprs <- stmt = do
		exprs' <- mapM fornex exprs
		return $ Function f exprs'
	| otherwise 				= do 
				return stmt

fornex expr
	| (Loc xp)      <- expr  = do
			xp' <- fornvar xp
			return (Loc xp')
	| Not xp <-expr 	= do
			xp' <- fornex xp
			return (Not xp')
	| Neg xp <-expr 	= do
			xp' <- fornex xp
			return (Neg xp')
	| Str _ <-expr 		= do 
				return expr
	| Const _ <-expr 	= do
				return expr
	| FuncCall st exprs <-expr 	= do
				exprs' <- mapM fornex exprs
				return $ FuncCall st exprs'
	| Add x y <- expr	= do
				x' <- fornex x
				y' <- fornex y
				return $ Add  x'  y'
	| Sub x y <- expr	= do
				x' <- fornex x
				y' <- fornex y
				return $ Add   x'  y'
	| Mul x y <- expr	=do
				x' <- fornex x
				y' <- fornex y
				return $  Mul  x'  y'
	| Div x y <- expr	= do
				x' <- fornex x
				y' <- fornex y
				return $  Div   x'  y'
	| Mod x y <- expr	= do
				x' <- fornex x
				y' <- fornex y
				return $  Mod   x'  y'
	| And x y <- expr	= do
				x' <- fornex x
				y' <- fornex y
				return $  And   x'  y'
	| Or x y <- expr	= do
				x' <- fornex x
				y' <- fornex y
				return $  Or  x'  y'
	| Eq x y <- expr	= do
				x' <- fornex x
				y' <- fornex y
				return $  Eq   x'  y'
	| Lt x y <- expr	= do
				x' <- fornex x
				y' <- fornex y
				return $  Lt   x'  y'
	| Gt x y <- expr	= do
				x' <- fornex x
				y' <- fornex y
				return $  Gt   x'  y'
	| Le x y <- expr	= do
				x' <- fornex x
				y' <- fornex y
				return $  Le   x'  y'
	| Ge x y <- expr	= do
				x' <- fornex x
				y' <- fornex y
				return $  Ge   x'  y'
	| Ne x y <- expr	= do
				x' <- fornex x
				y' <- fornex y
				return $  Ne   x'  y'
	| otherwise		= do
				return expr


--fornvar:: M m => Variable -> m Variable 
fornvar v =do
	st@(scp, mp,i) <- get
	let scope = fromJust $ M.lookup (standardizeArrays v) (mp:: M.Map Variable [Scoped])
	return $ Scopedvar scope v
	where
		standardizeArrays (Varray str _) = (Varray str (Const 0))
		standardizeArrays x = x



stripper (Prg code) = do
	code' <-  mapM fornicake code
	return $ Prg code'

indians stmt 	
        | DFun name params bod		<- stmt = concatMap indians bod
        | If expression thens elses 	<- stmt = concatMap indians thens ++ concatMap indians elses
        | While cond bod		<- stmt = concatMap indians bod
        | ForLoop i start end bod		<- stmt = [i] ++ concatMap indians bod 
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
        | ForLoop i start end bod		<- stmt = do
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
        | ForLoop i start end bod		<- stmt = do	
				bod' <- mapM (drip sl el) bod
				sl $ForLoop i start end bod'
        | otherwise 				= do 
				sl stmt


fortress for@(ForLoop i start end bod) = do 
	bod' <- mapM fornicake bod
	vars<-get
	let     is:: [(Variable,Expression)]
		is = execState (drip induct (return) for) []
	ars <- return $ execState (drip (extractArrs) (return) for) []
	risky <-return $ nub $ filter (isInductive $ map fst is) ars
	if parallelizable (map fst is) (map snd is) risky
		then return $ Parafor i start end bod'
		else return $ ForLoop i start end bod'

induct for@(ForLoop i start end bod) = do
	vars<-get 
	put $ vars ++ [(i,end)]
	return for
induct x = do
	return x

--affine (i:j:xs) (


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
	
	| ForLoop  _ _ expr _ <- stmt = do 
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


--parallelizable:: [Variable] -> [Access] -> Bool
parallelizable is ends axs = unsafePerformIO $ do
--putStrLn $ show (comb ws rs)
	return $ and $ map (bjork is) $ comb ws rs
	where
	 comb:: [([[Int]],[Int])] -> [([[Int]],[Int])] -> [(([[Int]],[Int]),([[Int]],[Int]))]
	 comb (x:xs) ys = (map (\yy -> (x,yy)) ys) ++ comb xs ys
	 comb [] ys = []
	 ws= nub $map (template is) $concatMap isWrite axs
	 rs= nub $map (template is) $concatMap isRead axs
--	 appTempt (Varray nm expr) = (nm,template is expr)
	 isWrite (Write x) 	= [x]
	 isWrite x 	        = []
	 isRead  (Read x)	= [x]
	 isRead x 	        = []

bjork:: [Variable]->(([[Int]],[Int]),([[Int]],[Int])) -> Bool
bjork (i:[]) (x@(m,v),y@(n,u))  
	| x == y = True
	| otherwise  = False
bjork (i:j:[]) (x@(m,v),y@(n,u)) 
	| x == y = True
	| otherwise  = False
{-
affinize (i:j:xs) axs = (ws, rs)
	where
	 ws=map template $concatMap isWrite axs
	 rs=map template $concatMap isRead axs
	 appTempt (Varray nm expr) = (nm,template [i,j] expr)
	 isWrite (Write x) 	= [x]
	 isWrite x 	        = []
	 isRead  (Read x)	= [x]
	 isRead x 	        = []
-}
--constant acces

template:: [Variable] -> Variable -> ([[Int]],[Int])

--simple ai+b access
template (i:_) (Varray nm e) 
	|(Add (Mul (Const a) (Loc i)) (Const b) ) <-e  =  aipb a b
	|(Add (Mul (Loc i) (Const a)) (Const b) ) <-e = aipb a b
	|(Add (Const b) (Mul (Const a) (Loc i))) <-e = aipb a b
	|(Add (Const b) (Mul (Loc i) (Const a))) <-e = aipb a b
	|(Add (Loc i) (Const b) ) <-e = aipb 1 b
	|(Add (Const b) (Loc i)) <-e = aipb 1 b
	|(Loc i) <-e = aipb 1 0



-- ai+bj access
template (i:j:_) (Varray nm e) 
	|(Add (Mul (Const a) (Loc i)) (Mul (Const b) (Loc j))) <-e = aibj a b
	|(Add (Mul (Loc i) (Const a)) (Mul (Const b) (Loc j))) <-e = aibj a b
	|(Add (Mul (Loc i) (Const a)) (Mul (Loc j) (Const b))) <-e = aibj a b
	|(Add (Mul (Const a) (Loc i)) (Mul (Loc j) (Const b))) <-e = aibj a b
	|(Add (Loc j) (Mul (Loc i) (Const a))) <-e = aibj a 1
	|(Add (Loc j) (Mul (Const a) (Loc i))) <-e = aibj a 1
	|(Add (Mul (Const a) (Loc i)) (Loc j)) <-e = aibj a 1
	|(Add (Mul (Loc i) (Const a)) (Loc j)) <-e = aibj a 1
	|(Add (Loc i) (Mul (Loc j) (Const b))) <-e = aibj 1 b
	|(Add (Loc i) (Mul (Const b) (Loc j))) <-e = aibj 1 b
	|(Add (Mul (Const b) (Loc j)) (Loc i)) <-e = aibj 1 b
	|(Add (Mul (Loc j) (Const b)) (Loc i)) <-e = aibj 1 b

aipb a b = ([[a]],[b])
aibj a b = ([[a,0],[0,b]],[0])


-- not worth doing right now
{-
template (i:j:_) (Varray nm e) =
	|() 	
	|(Add (Mul (Const a) (Loc i)) (Mul (Const b) (Loc j))) <-e = aibj a b
	|(Add (Mul (Loc i) (Const a)) (Mul (Const b) (Loc j))) <-e = aibj a b
	|(Add (Mul (Loc i) (Const a)) (Mul (Loc j) (Const b))) <-e = aibj a b
	|(Add (Mul (Const i) (Loc a)) (Mul (Loc j) (Const b))) <-e = aibj a b
	|(Add (Loc j) (Mul (Loc i) (Const a))) <-e = aibj a 1
	|(Add (Loc j) (Mul (Const a) (Loc i))) <-e = aibj a 1
	|(Add (Mul (Const a) (Loc i)) (Loc j)) <-e = aibj a 1
	|(Add (Mul (Loc i) (Const a)) (Loc j)) <-e = aibj a 1
	|(Add (Loc i) (Mul (Loc j) (Const b))) <-e = aibj 1 b
	|(Add (Loc i) (Mul (Const b) (Loc j))) <-e = aibj 1 b
	|(Add (Mul (Const b) (Loc j)) (Loc i)) <-e = aibj 1 b
	|(Add (Mul (Loc j) (Const b)) (Loc i)) <-e = aibj 1 b

e
-}

--	| <-e 
---	| <-e 
--	| <-e 
--	| <-e 
--	| <-e 
--	| <-e 
--






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


                                (LastOther (ForBranch _ _ _ b1 b2)) -> let
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
				(LastOther (ForBranch _ _ _ b1 b2)) -> let
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
	
