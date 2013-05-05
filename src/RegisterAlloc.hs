module RegisterAlloc where 

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


type StringState = M.Map String String
--insert = M.insert
--fj x = fromJust $ case x of
--		Nothing -> Debug.Trace.traceShow x Nothing
--		x -> x
data GlobalTable = GlobalEntry {getName::String} 
data LocalTable = LocalEntry {getScope::String, getSymbol::String} 

--navigate :: (Show a) => a -> LGraph ProtoASM ProtoBranch -> LGraph ProtoASM ProtoBranch
navigate globals funmap cfg = unsafePerformIO $ do 
		let cfg' = focus (BID "main" ) cfg 
		let (_,navret)= kruise cfg (stVarsCollect) []
		--let navret = navigate' cfg ["main"] $ fgFocus  cfg' 
		let bid2scope = nub $ [(BID "start_0", "global")] ++ map (\ (b,s, _)-> (b,s)) navret
		
--		putStrLn $ show navret
		let 	convertVariableToVar (Var sym) = (Symbol sym)
			convertVariableToVar (Varray sym (Const i)) = (Array sym (Literal i))
		let scope2var = nub $ map (\ (_,s,v)-> (s,v)) (navret ++ map (\x -> ((BID "global"), "global", convertVariableToVar x )) globals)
--		putStrLn $ show $ mappify (M.empty) bid2scope
--		putStrLn $ show $ mappify (M.empty) scope2var
--		putStrLn $ show funmap 
--		cfgWithVariableLabels <- return $ fmapGraph (translateWithMap bid2scope) (translateBranchWithMap bid2scope) cfg 
		cfgWithVariableLabels <- return $ fst $ trickle cfg (scoper) M.empty
		putStrLn $ show cfgWithVariableLabels
		let (_,vars') = kruise cfgWithVariableLabels extractVars []
		let vars = nub vars'
		let vardata = concatMap datifyVars vars 
		strings <- return $ nub $ map (\(EvilString x) -> x)$findAllStrings cfgWithVariableLabels
		epilog <- return $ (makeDataSection strings) ++ vardata
	--	pprIO cfg
		wrongarrcfg <- return $ mapLGraphNodes (replaceStrings) (\_ x -> (([],[]),x)) cfgWithVariableLabels
		finalcfg <- return $ mapLGraphNodes (fixArrays) (fixZLastArrays) wrongarrcfg
		return (prolog,finalcfg,epilog)
	where 	mappify:: (Ord a, Ord k) => (M.Map a [k]) -> [(a,k)]-> (M.Map a [k])
		mappify mp ((b,s):xs) = mappify (M.alter (addorappend s) b mp) xs 
		mappify mp [] = mp
		addorappend s (Just x) = Just $ x ++ [s]
		addorappend s Nothing = Just $ [s]
		prolog = ".global main\n"

isvar x@(Symbol _) = True
isvar x@(Array _ _) = True
isvar x = False


extractVars bid scope p = do
	vals<-get 
	put $ vals ++ (filter isvar $ concatMap values p)
	return p

datifyVars y = case y of 
	(Symbol y') -> ".comm " ++ y'++", 8\n"
	(Array y' (Literal x')) -> ".comm "  ++ y' ++ ", " ++(show $ x' *8 ) ++"\n"  
	_ ->"" 
		

--scoper:: (MonadState (M.Map Value String) m) => BlockId -> [String] -> [ProtoASM] -> m [ProtoASM]
scoper bid scope instrs = do
	premap <- get
	varmap <- return $ (updatemap premap) 
	put varmap 
	return $ concatMap ((fixInstructionInputs (mapswap varmap))) instrs
		
	where
		mapswap:: M.Map Value String -> Value -> Value
		mapswap vmp v@(Symbol str) = Symbol $ prescope prefix ++ "_" ++ str
			where prefix = fj $ M.lookup v vmp
		mapswap vmp v@(Array str va) = Array (prescope prefix ++ "_" ++ str) va
			where prefix = fj $ M.lookup v vmp
		mapswap vmp v = v
		decls = concatMap isDecl instrs
		isDecl (Dec' v) =  [v]
		isDecl _ =  []
		updatemap:: M.Map Value [Char] -> M.Map Value [Char]
		updatemap mp = updatemap' decls mp
		updatemap':: [Value] -> M.Map Value [Char] -> M.Map Value [Char]
		updatemap' (x:xs) mp = M.insert x (head scope) (updatemap' xs mp)
		updatemap' [] mp = mp 
		prescope pre = intercalate "_" $reverse$dropWhile (/=pre) scope 




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
			output = case instr of 
					(Dec' v)	->	(Dec' v) 	
					(Mov' v1 v2)	->	(Mov' (fix v1) (fix v2))
					(Neg' v)	->	(Neg' (fix v))
					(And' v1 v2)	->	(And' (fix v1) (fix v2))
					(Or'  v1 v2)	->	(Or'  (fix v1) (fix v2))
					(Add' v1 v2)	->	(Add' (fix v1) (fix v2))
					(Sub' v1 v2)	->	(Sub' (fix v1) (fix v2))
					(Mul' v1 v2)	->	(Mul' (fix v1) (fix v2))
					(Div' v1 v2)	->	(Div' (fix v1) (fix v2))
					(Lt'   v1 v2)	->	(Lt'   (fix v1) (fix v2))
					(Gt'   v1 v2)	->	(Gt'   (fix v1) (fix v2))
					(Le'   v1 v2)	->	(Le'   (fix v1) (fix v2))
					(Ge'   v1 v2)	->	(Ge'   (fix v1) (fix v2))
					(Eq'   v1 v2)	->	(Eq'   (fix v1) (fix v2))
					(DFun'   name vs)	->	DFun' name $ map fix vs
					(Ne'   v1 v2)	->	(Ne'   (fix v1) (fix v2))
					(Not'  v)	->	(Not'  (fix v))
					(Ret'  v)	->	(Ret'  (fix v))
					(Call' _)   	->	instr
					(Str' v)	->	(Str' (fix v))
					(Cmp' v1 v2)	->	(Cmp' (fix v1) (fix v2))
					(Je' _)		->	instr
					(Jmp' _)	->	instr
					(Push' v)	->	(Push' (fix v))
					(Pop' v)	->	(Pop' (fix v))



navigate' :: LGraph ProtoASM ProtoBranch -> [String] -> ZBlock ProtoASM ProtoBranch -> [(BlockId, String, Value)]
navigate' c scope zcfg = collectVars c scope zcfg


--scoping vars zcfg = case z 

--body= zbTail



--vars ++ map navigateFunction collectFunctionCalls
getBlock :: LGraph m l -> BlockId -> Maybe (ZBlock m l)
getBlock (LGraph eid blocks) blockid =  case lookupBlock blockid blocks of
	 Nothing -> Nothing
	 (Just blk) -> Just $ fgFocus $ ZGraph eid (unzipB blk) (removeBlock blockid blocks)

collectVars :: LGraph ProtoASM ProtoBranch -> [String] -> ZBlock ProtoASM ProtoBranch -> [(BlockId, String, Value)]
collectVars c scope zcfg = scopeVars ++ functionVars
	where   	
		scopeVars = map (\(bd,x)-> (bd,(head scope),x))$ filter isVar $concatMap values' $ middles
		functionCalls = nub $ concatMap (\(_,(Call' str)) -> if (not $ elem str scope) then [str] else [])$ filter isCall middles
		functionVars = concatMap (\ name -> collectVars (c) [name] (fj $ getBlock c (BID name))) $ filter ( \name -> isJust $ getBlock c (BID name)) functionCalls 
		isCall (_,(Call' str)) = True
		isCall _ = False
		isVar (_,a@(Symbol _)) = True
		isVar (_,a@(Array _ _)) = True
--		isVar (_,a@(Array _ _)) = True
		isVar _ = False
		middles = zipThroughB c zcfg 

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
		(Div' v1 v2)	->	[v1,v2]
		(Lt'   v1 v2)	->	[v1,v2]
		(Gt'   v1 v2)	->	[v1,v2]
		(Le'   v1 v2)	->	[v1,v2]
		(Ge'   v1 v2)	->	[v1,v2]
		(Eq'   v1 v2)	->	[v1,v2]
		(Ne'   v1 v2)	->	[v1,v2]
		(DFun' _ vs)	->	vs
		(Not'  v)	-> 	[v] 
		(Ret'  v)	->	[v]
		(Call' _)   	->	[]
		(Str' v)	-> 	[v]
		(Cmp' v1 v2)	-> 	[]
		(Je' _)		->	[]
		(Jmp' _)	->	[]
		(Push' v)	->	[v]
		(Pop' v)	->	[v]

zipThroughB :: LGraph ProtoASM ProtoBranch -> ZBlock ProtoASM ProtoBranch -> [(BlockId, ProtoASM)]
zipThroughB  c b = zipThroughBState [] c b 

zipThroughBState scope c b = case zbTail b of 
		(ZTail m _) -> ((getBlockId b),m):(zipThroughBState (b:scope) c (nextEdge b))
		(ZLast (LastOther (Jump' bs) ))->  if not (elem b scope)
				then zipThroughBState (b:scope) c $ fj $ getBlock c bs 
				else []
		(ZLast (LastOther (If' expr (b1:b2:_)) ))-> if not (elem b scope) 
				then (map (\z -> ((getBlockId b), z)) expr) ++ (zipThroughBState (b:scope) c $fj $getBlock c b2 ) ++ (zipThroughBState (b:scope) c $ fj $ getBlock c b1 ) -- fgFocus $ focus b1 c)
				else []
		(ZLast (LastOther (While' expr (b1:b2:_)) ))-> if not (elem b scope)
				then (map (\z -> ((getBlockId b), z)) expr) ++ (zipThroughBState (b:scope) c $ fj$ getBlock c b2) ++ (zipThroughBState (b:scope) c $ fj $ getBlock c b1 ) --fgFocus $ focus b1 c)
				else []
		(ZLast (LastOther (InitialBranch' bs )))-> if not (elem b scope) 
				then concatMap (\x -> zipThroughBState (b:scope) c $ fj $ getBlock c x) bs
				else []
		_ -> []
--		(ZLast (LastOther (Jump' bs) ))->  zipThroughB c $ fromJust $ getBlock c bs 
--		(ZLast (LastOther (If' expr (b1:b2:_)) ))-> (map (\z -> (b1, z)) expr) ++ (zipThroughB c $fromJust $getBlock c b2 ) ++ (map (\x -> (b1,x)) $zipThroughB' c $ fgFocus $ focus b1 c)
--		(ZLast (LastOther (While' expr (b1:b2:_)) ))-> (map (\z -> (b1, z)) expr) ++ (zipThroughB c $ fromJust$ getBlock c b2) ++ (map (\x -> (b1,x))$zipThroughB' c $fgFocus $ focus b1 c)
--		(ZLast (LastOther (InitialBranch' bs )))-> concatMap (\x -> zipThroughB c $ fromJust$ getBlock c x) bs
--		_ -> []
        --
-- A version that doesn't jump to other blocks
--zipThroughB' :: ZBlock a l -> [a]
zipThroughB'  b = case zbTail b of 
		(ZTail m _) -> m:(zipThroughB' (nextEdge b))
		_ -> []
{-
lowIRtoAsm :: (Show l, PrettyPrint l, LastNode l) => LGraph ProtoASM l -> IO (LGraph ProtoASM l)
lowIRtoAsm lowir = do
	let zcfg = focus (lgEntry lowir) lowir
	let strSt = M.empty
	let strlist = unsafePerformIO $ newIORef []
	let out = graftBlocks lowir
	let cds = findAllStrings zcfg
	putStrLn $ show $ map getString cds
	void $ navBlock $ fgFocus zcfg
	return out
-}


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
					(Div' v1 v2)	->	(Div' (fix v1) (fix v2))
					(Lt'   v1 v2)	->	(Lt'   (fix v1) (fix v2))
					(Gt'   v1 v2)	->	(Gt'   (fix v1) (fix v2))
					(Le'   v1 v2)	->	(Le'   (fix v1) (fix v2))
					(Ge'   v1 v2)	->	(Ge'   (fix v1) (fix v2))
					(Eq'   v1 v2)	->	(Eq'   (fix v1) (fix v2))
					(Ne'   v1 v2)	->	(Ne'   (fix v1) (fix v2))
					(Not'  v)	->	(Not'  (fix v))
					(Ret'  v)	->	(Ret'  (fix v))
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


-- ///navigate state fm fl zcfg = do

navBlock :: (Show l, Show m) => ZBlock m l -> IO ()
navBlock zcfg = do
		putStrLn $ show (lastEdge zcfg)
{--
		case lastEdge of
			(ZLast $ If' _ _ _)
		navigateZtails state fm fl main
		nextEdge b

	
navigateZTailMiddles :: (PrettyPrint l, PrettyPrint m1, PrettyPrint m2, LastNode l) =>
    (m1 -> [m2]) -> ZTail m1 l -> ZTail m2 l
navigateZTailMiddles f ztail = navigateZTail state f (\x -> ([], x)) ztail

navigateZTail:: (PrettyPrint l1, PrettyPrint l2, PrettyPrint m1, PrettyPrint m2, LastNode l1, LastNode l2) =>
    (m1 -> [m2]) -> (ZLast l1 -> ([m2], ZLast l2)) -> ZTail m1 l1 -> ZTail m2 l2

navigateZTail state fm fl ztail = let zl = getZLast ztail
                           (state',endMids, zl') = (fl state zl) in
                              ztailFromMiddles (mappedMiddles ++ endMids) zl'
    where mappedMiddles = concatMap fm $ ztailCollectMiddles ztail

ztailCollectMiddles :: (PrettyPrint m, PrettyPrint l, LastNode l) =>
    ZTail m l -> [m]
ztailCollectMiddles (ZLast _) = []
ztailCollectMiddles (ZTail m zt) = m : ztailCollectMiddles zt

--}	 
