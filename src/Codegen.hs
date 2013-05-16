module Codegen where 




import Varmarker
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
import Parallel

--navigate :: (Show a) => a -> LGraph ProtoASM ProtoBranch -> LGraph ProtoASM ProtoBranch

-- sequential operations that navigate through the CFG and prepair assembly
navigate globals funmap cfg = unsafePerformIO $ do 
		let cfg' = focus (BID "main" ) cfg 
		
		-- removes variables so we can make a data section
		let (_,vars') = kruise cfg extractVars []
		let vars = nub vars'

		
		let appendGlobalLabel x = Scoped [Global] x
		let vardata = (concatMap datifyVars (vars ++ map (appendGlobalLabel.var2val) globals) )
			
		-- handles strings strings
		strings <- return $ nub $ map (\(EvilString x) -> x)$findAllStrings cfg
		finalcfg <- return $ mapLGraphNodes (replaceStrings) (\_ x -> (([],[]),x)) cfg
		
		-- Data section
		epilog <- return $ (makeDataSection strings) ++ vardata ++ 
			"\n.comm t0,8\n"
			++".comm t1,8\n"
			++".comm t2,8\n"
			++".comm t3,8\n"
			++".comm t4,8\n"
			++".comm t5,8\n"
			++".comm t6,8\n"
			++".comm t7,8\n"
			++".comm p1,32\n"
			++".comm p2,32\n"
			++".comm p3,32\n"
			++".comm p4,32\n"
			++".comm p5,32\n"
			++".comm p2,32\n"
			++".comm p2,32\n"
			++".comm p2,32\n"
			++".comm p2,32\n"
			++".comm p2,32\n"
			++".comm p2,32\n"
			++".comm p2,32\n"
		
		-- Adds enter commands at the begining of every function
		entercfg <- return $ cruise finalcfg addEnter 

		-- Peephole optimization : mov r1 , r2; mov r2 r3 -> move r1 , r3
		let apptilfalse f x = case f x of
				(x',True) -> apptilfalse f x'
				(x',False) -> x'
		zigcfg <- return $ apptilfalse (\gg -> kruise gg regZigZag False) entercfg
		
		-- Peephoel optimaztion : gets rid of useless push and pops	
--		poppushcfg <- return $ fst $ esiurk zigcfg popAlot M.empty
				
		-- replaces breaks and continues with jumps to labels
		outcfg <-return$ fst $ trickleLast zigcfg replaceBreakContinue Nil 
		-- output to be printed
		return (prolog, outcfg,epilog)
	where 	mappify:: (Ord a, Ord k) => (M.Map a [k]) -> [(a,k)]-> (M.Map a [k])
		mappify mp ((b,s):xs) = mappify (M.alter (addorappend s) b mp) xs 
		mappify mp [] = mp
		addorappend s (Just x) = Just $ x ++ [s]
		addorappend s Nothing = Just $ [s]
		prolog = ".global main\n"
		var2val (Var str) = Symbol str
		var2val (Varray str (Const i)) = Array str (Literal i)


scopeMidir midir globals funmap = fst $ hemorhage midir (scoper funmap) (lfixBranch funmap) globalmap
		where
			 globalist =  map (\x-> Scopedvar [Global] x)$ globals
			 standardizeArrays (Varray sym _) = (Varray sym (Const 0))
		    	 standardizeArrays x = x
			 globalmap =  insertListMap ( map (\(x) -> ((standardizeArrays x) , [Global])) globalist) $ M.empty
		

{-
varMap cfg = execState (kruise varMap' cfg) M.empty
	
varMap':: State ((M.Map String BlockId),(M.Map (BlockId String) BlockId))
varMap' bid scope p =
	(var2bid,bidvar2bid)<- get 
	defVars <- decls
	var2bid' <- updatemap' defVars var2bid
	blockvars <- return $ map name $ filter isVar $concatMap values p 
	let varbid v
		| Just bid <- M.lookup v var2bid' = bid
	put $ insertListMap $ map (\v-> ((bid,name v), varbid v)) blockvar
	return $ p
		
	where
		params = extractParams instrs
		extractParams ((DFun' _ v):xs) = v
		extractParams _ = []
		decls = (concatMap isDecl instrs) ++ params
		isDecl (Dec' v) =  [v]
		isDecl _ =  []
		updatemap':: [Value] -> M.Map Value [Char] -> M.Map Value [Char]
		updatemap' (x:xs) mp = M.insert x bid (updatemap' xs mp)
		updatemap' [] mp = mp 
-}


 
-- add an enter instruction at the begining of all functions
addEnter:: BlockId -> [ProtoASM] -> [ProtoASM]
addEnter bid p = do
	ae p
	where 	ae:: [ProtoASM]->[ProtoASM]
		ae ((x@(DFun' _ _)):xs) = x:(Enter' 10):xs
		ae y = y 
		

-- knows what registers functions use, and only pops and pushs as necessary
popAlot bid scope p = do
	mapa<- get
	let preregs = case M.lookup (head scope) mapa of
			Just x  -> x
			Nothing -> []
	let 	aep ((i@(Push' x)):xs) = do
					utilize <- get 
					next <- aep xs
					return $ if elem x utilize
						then  (i:next)
				  		else next 
		aep  ((i@(Pop' x)):xs) = do 
					utilize <- get 
					next <- aep xs
					return $ if elem x utilize
						then  (i:next)
				  		else  next
		aep (x:xs) = do
			regs <- get
			let command = command' (hungryLogic x)
			    command' [x,y] = [(filter isRegister x), (filter isRegister y)] 
			    command' x = x 
			
			put $ process command regs
 			next <- (aep xs)	
			return $ x:next
			where 
				process [include,evict] regs = union (regs \\ evict) include
				process x regs = regs
		aep [] = do 
			return [] 
	let (p', regsused) = runState (aep (reverse p)) preregs
	put $ M.insert (head scope) regsused mapa
	return $ reverse p'

-- kinda like livelyness analysis, which registers have comands that care about their
-- value after a function call.
hungryLogic instr = case instr of   -- [(ADD) (EVICT)]
		(Mov' v1 v2)	->	[[v1],[v2]]
		(Neg' v)	->	[[v],[]]
		(And' v1 v2)	->	[[v1,v2],[]]
		(Or'  v1 v2)	->	[[v1,v2],[]]
		(Add' v1 v2)	->	[[v1,v2],[]]
		(Sub' v1 v2)	->	[[v1,v2],[]]
		(Mul' v1 v2)	->	[[v1,v2],[]]
		(Div' v1)	->	[[v1],[]]
		(CMovl'   v1 v2)	->	[[v1,v2],[]]
		(CMovg'   v1 v2)	->	[[v1,v2],[]]
		(CMovle'   v1 v2)	->	[[v1,v2],[]]
		(CMovge'   v1 v2)	->	[[v1,v2],[]]
		(CMove'   v1 v2)	->	[[v1,v2],[]]
		(Ne'   v1 v2)	->	[[v1,v2],[]]
		(DFun' _ vs)	->	[[],[]]
		(Not'  v)	-> 	[[v],[]] 
		(Call' _)   	->	[[],[]]
		(Str' v)	-> 	[[],[]]
		(Cmp' v1 v2)	-> 	[[v1,v2],[]]
		(Je' _)		->	[]
		(Jmp' _)	->	[]
		x		-> 	[]


-- reg mov zigzag peephole optimization
regZigZag bid scope p = do
	let (state,out) = ae p
	put state
	return out
	where  
		ae ((m@(Mov' x y )):(f@(Mov' x' y')):xs) = if y == x' && isRegister y && (not $ (memlocation x) && (memlocation y'))
			then (True,(snd$ ae ((Mov' x y'):xs)))
			else  let ae' = ae (f:xs) in ((fst ae'),m:(snd ae'))
		ae (x:xs) = ((fst ae'), x:(snd ae'))
			where ae' = ae xs
		ae x = (False, x)
		memlocation (Symbol _) = True 
		memlocation (Dereference _ _) = True 
		memlocation (Array _ _) = True 
		memlocation (Stack _) = True 
		memlocation (EvilSymbol _) = True 
		memlocation x = False

-- registers which are used in the scope
regUsage bid scope p = do
	regs <- get
        put $putintomap scope2reg regs
	return p
	where 	vals = concatMap valuesNoStack p
		regused = filter isRegister $ concatMap converDerefs vals
		converDerefs (Dereference r1 r2) = [r1,r2]
		converDerefs x = [x]		
		scope2reg = map (\x -> ((head scope) , x)) regused
		putintomap ((x,y):xs) mp = let newmap = (putintomap xs mp) 
				in case M.lookup x newmap of
					Just prev -> M.insert x (nub (y:prev)) newmap
					Nothing -> M.insert x [y] newmap
		putintomap [] mp = mp

-- extracts values, ignoring push and pops
valuesNoStack instr = case instr of
		(Dec' v)	->	[v]
		(Mov' v1 v2)	->	[v1,v2]
		(Neg' v)	->	[v]
		(And' v1 v2)	->	[v1,v2]
		(Or'  v1 v2)	->	[v1,v2]
		(Add' v1 v2)	->	[v1,v2]
		(Sub' v1 v2)	->	[v1,v2]
		(Mul' v1 v2)	->	[v1,v2]
		(Div' v1)	->	[v1]
		(CMovl'   v1 v2)	->	[v1,v2]
		(CMovg'   v1 v2)	->	[v1,v2]
		(CMovle'   v1 v2)	->	[v1,v2]
		(CMovge'   v1 v2)	->	[v1,v2]
		(CMove'   v1 v2)	->	[v1,v2]
		(Ne'   v1 v2)	->	[v1,v2]
		(DFun' _ vs)	->	vs
		(Not'  v)	-> 	[v] 
		(Call' _)   	->	[]
		(Str' v)	-> 	[v]
		(Cmp' v1 v2)	-> 	[]
		(Je' _)		->	[]
		(Jmp' _)	->	[]
		x		-> 	[]


isvar x@(Symbol _) = True
isvar x@(Array _ _) = True
isvar x = False


extractVars bid scope p = do
	vals<-get 
	put $vals ++ (filter isvar $ concatMap values p)
	return p

datifyVars y = case y of 
	(Symbol y') -> ".comm " ++ y'++", 8\n"
	(Array y' (Literal x')) -> ".comm "  ++ y' ++ ", " ++(show $ x' *8 ) ++"\n"  
	_ ->"" 
		


replaceBreakContinue last bid scope instrs = do
	loop <-get
	newloop <- return $ case last of
		(While' _ _)	-> last
		_ 		-> loop
	put newloop
	let (b1,b2) = case loop of
		 (While' _ (ba:bb:xs)) -> (ba,bb)
		 --(For' _ _ (ba:bb:xs)) -> (ba,bb)
		 _ -> ((BID "NIGERIA"),(BID "NIGERIA")) -- please please please NEVER happen!   	
	let	fixit (Break') = Jmp' b2  	
		fixit (Continue') = Jmp' $ BID $ testLabel b1
		fixit x = x 
        return $ map fixit instrs




-- scopifies vars
--scoper:: (MonadState (M.Map Variable [Scoped]) m) => M.Map String [Variable] -> BlockId -> [String] -> [Statement] -> m [Statement]
scoper funmap bid scope instrs =  do
	premap <- get
	varmap <- return $  (updatemap premap) 
	put$ Debug.Trace.trace (getStr bid ++ (show varmap)) varmap 
	return $ map (fixStatement (fixExpression (mapswap varmap)) (mapswap varmap)) instrs
		
	where
		mapswap vmp v@(Var str) = Scopedvar prefix v
			where prefix = fj 8 $ M.lookup v vmp
		mapswap vmp v@(Varray str va) = Scopedvar prefix v
			where prefix = case M.lookup (Varray str (Const 0)) vmp of
				Just x -> x
				Nothing -> []	
-- important convention array always RAX in tables!
	--	mapswap:: M.Map Value String -> Value -> Value
--		mapswap vmp v@(Var str) = Scopedvar (prescope $scopify $ head scope) v
--			where prefix = fj$ M.lookup v vmp
--		mapswap vmp v@(Varray str va) = Scopedvar (prescope $ scopify $ head scope) v
--			where prefix = fj $ M.lookup (Varray str (Const 0)) vmp -- important convention array always RAX in tables!
		mapswap vmp v = v
		params = extractParams instrs
		extractParams ((DFun _ v _):xs) = v
		extractParams _ = []
		decls = (concatMap isDecl instrs) ++ params
		isDecl (DVar v) =  [v]
		isDecl _ =  []
		updatemap:: M.Map Variable [Scoped] -> M.Map Variable [Scoped]
		updatemap':: [Variable]-> M.Map Variable [Scoped] -> M.Map Variable [Scoped]
		updatemap mp = updatemap' decls mp
	--	updatemap':: [Value] -> M.Map Value [Char] -> M.Map Value [Char]
		updatemap' (x:xs) mp 
			| (Varray nm _) <-x = M.insert (Varray nm (Const 0))  (map scopify scope) (updatemap' xs mp)
			| otherwise = M.insert x (map scopify scope) (updatemap' xs mp)
		updatemap' [] mp = mp 
		prescope pre = reverse$ dropWhile (/= pre) $ map scopify scope
		scopify "global" = Global 
		scopify x 
			| Just _ <-M.lookup x funmap = Func x
			| otherwise = Loop x 

lfixBranch funmap lst scope = do 
		varmap <- get
		let lv = mapswap varmap
		let le = fixExpression lv
		case lst of 
			(IfBranch e b1 b2) -> return $ IfBranch (le e) b1 b2
			(WhileBranch e b1 b2) -> return $ WhileBranch (le e) b1 b2
			(ForBranch v s e b1 b2) -> return $ ForBranch (lv v) (le s) (le e) b1 b2
			(ParaforBranch v s e b1 b2) -> return $ ParaforBranch (lv v) (le s) (le e) b1 b2
			x -> return x
    where mapswap vmp v@(Var str) = Scopedvar (prescope $scopify $ head scope) v
            where prefix = fj 20$ M.lookup v vmp
          mapswap vmp v@(Varray str va) = Scopedvar (prescope $ scopify $ head scope) v
            where prefix = fj 21 $ M.lookup (Varray str (Const 0)) vmp -- important convention array always RAX in tables!
          mapswap vmp v = v
          prescope pre = reverse$ dropWhile (/= pre) $ map scopify scope
          scopify "global" = Global 
          scopify x 
            | Just _ <-M.lookup x funmap = Func x
            | otherwise = Loop x 
		

fixStatement le lv stmt   
		| Set v e <-stmt= Set (lv v) (le e)
                | Return e<-stmt= Return (le e)
                | DVar v  <-stmt= DVar $ lv v 
                | Callout name prams <-stmt= Callout name (map le prams)
                | Function name prams<-stmt= Function name (map le prams)
		| If cond t e  <-stmt= If (le cond) t e
		| While cond b <-stmt= While (le cond) b
		| ForLoop i s end b <-stmt= ForLoop (lv i) (le s) (le end) b
		| Parafor i s end b <-stmt= Parafor (lv i) (le s) (le end) b
		| DFun n params body <-stmt = DFun n (map lv params) (map (fixStatement le lv) body)
		| otherwise = stmt

fixExpression l expr
	| c@(Const _) <- expr = c 
	| c@(Str _) <- expr = c 
	| c@(FuncCall nm params) <- expr = FuncCall nm (map (fixExpression l) params) 
	| c@(Not i) <- expr = Not $ fixExpression l i 
	| c@(Neg i) <- expr = Not $ fixExpression l i
	| Add ex ey <- expr = Add (fixExpression l ex) (fixExpression l ey)
        | Sub ex ey <- expr = Sub (fixExpression l ex) (fixExpression l ey)
        | Mul ex ey <- expr = Mul (fixExpression l ex) (fixExpression l ey)
        | Div ex ey <- expr = Div (fixExpression l ex) (fixExpression l ey)
        | Mod ex ey <- expr = Mod (fixExpression l ex) (fixExpression l ey)
        | And ex ey <- expr = And (fixExpression l ex) (fixExpression l ey)
        | Or ex ey <- expr = Or  (fixExpression l ex) (fixExpression l ey)
        | Eq  ex ey <- expr = Eq  (fixExpression l ex) (fixExpression l ey)
        | Lt  ex ey <- expr = Lt  (fixExpression l ex) (fixExpression l ey)
        | Gt  ex ey <- expr = Gt  (fixExpression l ex) (fixExpression l ey)
        | Le  ex ey <- expr = Le  (fixExpression l ex) (fixExpression l ey)
        | Ge  ex ey <- expr = Ge  (fixExpression l ex) (fixExpression l ey)
        | Ne  ex ey <- expr = Ne  (fixExpression l ex) (fixExpression l ey)
	| FuncCall nm prms <- expr = FuncCall nm (map (fixExpression l) prms)
	| (Loc v) <- expr = Loc$  l v  

stVarsCollect bid scope p = do
	vars <- get
	newvars <- return $ newvars
	put $ vars ++ (map (\x->(bid,(head scope),x)) newvars) 
	return p
     where
	 allvals = concatMap values p 
	 newvars = filter isVar allvals
	 isVar x@(Symbol _) = True
	 isVar x@(Array _ _) = True
	 isVar x = False



makeDataSection strings = ".data\n" ++ strings'
		where
			strings' = concatMap (\x -> "." ++ (getHashStr x) ++ ": " ++ ".string " ++ (show x) ++ "\n" ) strings


replaceStrings bid instruction = fixInstructionInputs fix instruction
		where 
			fix (EvilString x) =  (EvilSymbol $ "." ++ (getHashStr x))
			fix x = x


--- not necessary anymore!

fixArrays _ i@(Dec' _) = [i]
fixArrays bid instruction = case hasArray of
				False -> [instruction]
				True  -> handleArray instruction
	where 
		 hasArray = arrs /= []
		 arrs = filter isArray $ values instruction 
		 isArray (Array _ _) = True
		 isArray _ = False
		 handleArray instr = (loadArr $head arrs) ++ fixInstructionInputs replaceWithReg15 instr
		 replaceWithReg15 (Array _ i) = Dereference  R15 i 
		 replaceWithReg15 x = x
		 loadArr (Array str x) = [(Mov' (EvilSymbol str) R15)] 
		
fixZLastArrays bid (LastOther (While' expr bs )) =  (([],[]),LastOther (While' newexpr bs))
	where newexpr = concatMap (fixArrays bid) expr
fixZLastArrays bid (LastOther (If' expr bs )) =  (([],[]), LastOther (If' newexpr bs)) 
	where newexpr = concatMap (fixArrays bid) expr
fixZLastArrays _ x = (([],[]),x)


translateWithMap bid2scope bid instr = fixInstructionInputs fix instr
		where
			fix (Symbol x) = (Symbol $ scope ++ "_" ++ x)
			fix (Array x y) = (Array ( scope ++ "_" ++ x) (fix y))
			fix x = x
			scope =  fromMaybe "" $ lookup bid bid2scope

translateBranchWithMap bid2Scope bid (LastOther (While' expr bs )) =  (([],[]),LastOther (While' newexpr bs))
	where newexpr = concatMap (translateWithMap bid2Scope bid) expr
translateBranchWithMap bid2scope bid (LastOther (If' expr bs )) =  (([],[]), LastOther (If' newexpr bs)) 
	where newexpr = concatMap (translateWithMap bid2scope bid) expr
translateBranchWithMap _ _ x = (([],[]),x)


translateLastWithMap bid2scope bid (LastOther (If' stmts bids)) = 
    ([], LastOther $ If' (concatMap (translateWithMap bid2scope bid) stmts) bids)
translateLastWithMap bid2scope bid (LastOther (While' stmts bids)) = 
    ([], LastOther $ While' (concatMap (translateWithMap bid2scope bid) stmts) bids)
translateLastWithMap bid2scope bid lastStmt = ([], lastStmt)


fixInstructionInputs fix instr = [output]
		where
			output = case  instr of 
					(Dec' v)	->	(Dec' v) 	
					(Mov' v1 v2)	->	(Mov' (fix v1) (fix v2))
					(Neg' v)	->	(Neg' (fix v))
					(And' v1 v2)	->	(And' (fix v1) (fix v2))
					(Or'  v1 v2)	->	(Or'  (fix v1) (fix v2))
					(Add' v1 v2)	->	(Add' (fix v1) (fix v2))
					(Sub' v1 v2)	->	(Sub' (fix v1) (fix v2))
					(Mul' v1 v2)	->	(Mul' (fix v1) (fix v2))
					(Div' v1)	->	(Div' (fix v1) )
					(CMovl'   v1 v2)	->	(CMovl'   (fix v1) (fix v2))
					(CMovg'   v1 v2)	->	(CMovg'   (fix v1) (fix v2))
					(CMovle'   v1 v2)	->	(CMovle'   (fix v1) (fix v2))
					(CMovge'   v1 v2)	->	(CMovge'   (fix v1) (fix v2))
					(CMove'   v1 v2)	->	(CMove'   (fix v1) (fix v2))
					(DFun'   name vs)	->	DFun' name $ map fix vs
					(Ne'   v1 v2)	->	(Ne'   (fix v1) (fix v2))
					(Not'  v)	->	(Not'  (fix v))
					(Call' _)   	->	instr
					(Str' v)	->	(Str' (fix v))
					(Cmp' v1 v2)	->	(Cmp' (fix v1) (fix v2))
					(Je' _)		->	instr
					(Jmp' _)	->	instr
					(Push' v)	->	(Push' (fix v))
					(Pop' v)	->	(Pop' (fix v))
					x 		->      x



values' :: (t, ProtoASM) -> [(t, Value)]
values' (bid, instr) = map (\x-> (bid, x)) (values instr)

values :: ProtoASM -> [Value]
values instr = case instr of
		(Dec' v)	->	[v]
		(Mov' v1 v2)	->	[v1,v2]
		(Neg' v)	->	[v]
		(And' v1 v2)	->	[v1,v2]
		(Or'  v1 v2)	->	[v1,v2]
		(Add' v1 v2)	->	[v1,v2]
		(Sub' v1 v2)	->	[v1,v2]
		(Mul' v1 v2)	->	[v1,v2]
		(Div' v1)	->	[v1]
		(CMovl'   v1 v2)	->	[v1,v2]
		(CMovg'   v1 v2)	->	[v1,v2]
		(CMovle'   v1 v2)	->	[v1,v2]
		(CMovge'   v1 v2)	->	[v1,v2]
		(CMove'   v1 v2)	->	[v1,v2]
		(Ne'   v1 v2)	->	[v1,v2]
		(DFun' _ vs)	->	vs
		(Not'  v)	-> 	[v] 
		(Call' _)   	->	[]
		(Str' v)	-> 	[v]
		(Cmp' v1 v2)	-> 	[]
		(Je' _)		->	[]
		(Jmp' _)	->	[]
		(Push' v)	->	[v]
		(Pop' v)	->	[v]
		x		-> 	[]
zipThroughB :: LGraph ProtoASM ProtoBranch -> ZBlock ProtoASM ProtoBranch -> [(BlockId, ProtoASM)]
zipThroughB  c b = zipThroughBState [] c b 

zipThroughBState scope c b = case zbTail b of 
		(ZTail m _) -> ((getBlockId b),m):(zipThroughBState (b:scope) c (nextEdge b))
		(ZLast (LastOther (Jump' bs) ))->  if not (elem b scope)
				then zipThroughBState (b:scope) c $ fj 10 $ getBlock c bs 
				else []
		(ZLast (LastOther (If' expr (b1:b2:_)) ))-> if not (elem b scope) 
				then (map (\z -> ((getBlockId b), z)) expr) ++ (zipThroughBState (b:scope) c $fj 11 $getBlock c b2 ) ++ (zipThroughBState (b:scope) c $ fj  12$ getBlock c b1 ) -- fgFocus $ focus b1 c)
				else []
		(ZLast (LastOther (While' expr (b1:b2:_)) ))-> if not (elem b scope)
				then (map (\z -> ((getBlockId b), z)) expr) ++ (zipThroughBState (b:scope) c $ fj 13$ getBlock c b2) ++ (zipThroughBState (b:scope) c $ fj 14 $ getBlock c b1 ) --fgFocus $ focus b1 c)
				else []
		(ZLast (LastOther (InitialBranch' bs )))-> if not (elem b scope) 
				then concatMap (\x -> zipThroughBState (b:scope) c $ fj 15 $ getBlock c x) bs
				else []
		_ -> []

zipThroughB'  b = case zbTail b of 
		(ZTail m _) -> m:(zipThroughB' (nextEdge b))
		_ -> []






getBlock (LGraph eid blocks) blockid = case lookupBlock blockid blocks of
	Nothing -> Nothing
	(Just blk) -> Just $ fgFocus $ ZGraph eid (unzipB blk) (removeBlock blockid blocks)



graftBlocks :: (PrettyPrint l, LastNode l) => LGraph ProtoASM l -> LGraph ProtoASM l
graftBlocks cfg = mapLGraphNodes ( values ) (\ _ x -> (([],[]),x)) cfg
	where	values ids instr = [instr']
				where instr' = case instr of
					(Dec' v)	->	(Dec' v) 	
					(Mov' v1 v2)	->	(Mov' (fix v1) (fix v2))
					(Neg' v)	->	(Neg' (fix v))
					(And' v1 v2)	->	(And' (fix v1) (fix v2))
					(Or'  v1 v2)	->	(Or'  (fix v1) (fix v2))
					(Add' v1 v2)	->	(Add' (fix v1) (fix v2))
					(Sub' v1 v2)	->	(Sub' (fix v1) (fix v2))
					(Mul' v1 v2)	->	(Mul' (fix v1) (fix v2))
					(Div' v1)	->	(Div' (fix v1))
					(CMovl'   v1 v2)	->	(CMovl'   (fix v1) (fix v2))
					(CMovg'   v1 v2)	->	(CMovg'   (fix v1) (fix v2))
					(CMovle'   v1 v2)	->	(CMovle'   (fix v1) (fix v2))
					(CMovge'   v1 v2)	->	(CMovge'   (fix v1) (fix v2))
					(CMove'   v1 v2)	->	(CMove'   (fix v1) (fix v2))
					(Ne'   v1 v2)	->	(Ne'   (fix v1) (fix v2))
					(Not'  v)	->	(Not'  (fix v))
					(Call' _)   	->	instr
					(Str' v)	->	(Str' (fix v))
					(Cmp' v1 v2)	->	(Cmp' (fix v1) (fix v2))
					(Je' _)		->	instr
					(Jmp' _)	->	instr
					(Push' v)	->	(Push' (fix v))
					(Pop' v)	->	(Pop' (fix v))
					where 	fix (EvilString str)  = (Label (getHashStr str))
						fix x = x
		strings = filter isString 
	        isString (EvilString str) = True 
	        isString _ 		  = False 


findAllStrings :: LastNode l => LGraph ProtoASM l -> [Value]
findAllStrings cfg = do 
		let blocks = postorderDFS cfg
		concat $ harvestStrings blocks
	where 	
		harvestStrings (b:blks) = (map (strings.values) (zipThroughB' $ unzipB b)) ++ (harvestStrings blks)
		harvestStrings _ = []
		strings = filter isString 
	        isString (EvilString str) = True 
	        isString _ 		  = False


