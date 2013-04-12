module RegisterAlloc where 

import MidIR
import Util
import qualified Data.Map as M
import ControlFlowGraph
import CFGConstruct
import CFGConcrete
import PrettyPrint
import Text.PrettyPrint.HughesPJ hiding (Str)
import Debug.Trace
import Control.Monad.State
import LowIR
import Data.IORef
import System.IO.Unsafe
import Data.Maybe
import Data.List

type StringState = M.Map String String
--insert = M.insert

data GlobalTable = GlobalEntry {getName::String} 
data LocalTable = LocalEntry {getScope::String, getSymbol::String} 

--navigate :: (Show a) => a -> LGraph ProtoASM ProtoBranch -> LGraph ProtoASM ProtoBranch
navigate globals funmap cfg = unsafePerformIO $ do 
		let cfg' = focus (lgEntry cfg ) cfg 
		let navret = navigate' cfg ["main"] $ fgFocus $ cfg' 
		let bid2scope = nub $ [(BID "start_0", "global")] ++ map (\ (b,s, _)-> (b,s)) navret
		let 	convertVariableToVar (Var sym) = (Symbol sym)
			convertVariableToVar (Varray sym (Const i)) = (Array sym (Literal i))
		let scope2var = nub $ map (\ (_,s,v)-> (s,v)) (navret ++ map (\x -> ((BID "global"), "global", convertVariableToVar x )) globals)
--		putStrLn $ show $ mappify (M.empty) bid2scope
--		putStrLn $ show $ mappify (M.empty) scope2var
--		putStrLn $ show funmap 
		cfgWithVariableLabels <- return $ mapLGraphNodes (translateWithMap bid2scope) (\_ x -> (([],[]),x)) cfg 
		strings <- return $ map (\(EvilString x) -> x)$findAllStrings cfgWithVariableLabels
		epilog <- return $ makeDataSection strings $ mappify (M.empty) $ scope2var
	--	pprIO cfg
		finalcfg <- return $ mapLGraphNodes (replaceStrings) (\_ x -> (([],[]),x)) cfgWithVariableLabels
		return (finalcfg,epilog)
	where 	mappify:: (Ord a, Ord k) => (M.Map a [k]) -> [(a,k)]-> (M.Map a [k])
		mappify mp ((b,s):xs) = mappify (M.alter (addorappend s) b mp) xs 
		mappify mp [] = mp
		addorappend s (Just x) = Just $ x ++ [s]
		addorappend s Nothing = Just $ [s]


makeDataSection strings scope2var = ".data\n" ++ variables ++ strings'
		where
			variables = concat $ concatMap (\(x,y) -> map (stringifyVars x ) y ) $ M.toList scope2var
			stringifyVars x y = case y of 
					(Symbol y') -> "." ++ x ++ "_" ++  y'++": .long 8\n"
					(Array y' (Literal x')) -> "." ++ x ++ "_" ++ y' ++ concat (replicate x' "  .long 8\n") 
					_ ->"" 
			strings' = concatMap (\x -> "." ++ (getHashStr x) ++ ": " ++ ".string " ++ (show x) ++ "\n" ) strings


replaceStrings bid instruction = fixInstructionInputs fix instruction
		where 
			fix (EvilString x) =  (Symbol $ "$." ++ (getHashStr x))
			fix x = x


translateWithMap bid2scope bid instr = fixInstructionInputs fix instr
		where
			fix (Symbol x) = (Symbol $ "$." ++ scope ++ "_" ++ x)
			fix (Array x y) = (Array ("$." ++ scope ++ "_" ++ x) (fix y))
			fix x = x
			scope =  fromMaybe "" $ lookup bid bid2scope

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
	
--vars ++ map navigateFunction collectFunctionCalls
getBlock :: LGraph m l -> BlockId -> Maybe (ZBlock m l)
getBlock (LGraph eid blocks) blockid =  case lookupBlock blockid blocks of
	 Nothing -> Nothing
	 (Just blk) -> Just $ fgFocus $ ZGraph eid (unzipB blk) (removeBlock blockid blocks)

collectVars :: LGraph ProtoASM ProtoBranch -> [String] -> ZBlock ProtoASM ProtoBranch -> [(BlockId, String, Value)]
collectVars c scope zcfg = scopeVars ++ functionVars
	where   	
		scopeVars = map (\(bd,x)-> (bd,(head scope),x))$ filter isVar $concatMap values' $ middles
		functionCalls = concatMap (\(_,(Call' str)) -> if (not $ elem str scope) then [str] else [])$ filter isCall middles
		functionVars = concatMap (\ name -> collectVars (c) (name:scope) (fromJust$ getBlock c (BID name))) $ filter ( \name -> isJust $ getBlock c (BID name)) functionCalls 
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

zipThroughB :: LGraph t ProtoBranch -> ZBlock t ProtoBranch -> [(BlockId, t)]
zipThroughB  c b = case zbTail b of 
		(ZTail m _) -> ((getBlockId b),m):(zipThroughB c (nextEdge b))
		(ZLast (LastOther (Jump' bs) ))->  zipThroughB c $ fromJust $ getBlock c bs 
		(ZLast (LastOther (If' _ (b1:b2:_)) ))-> (zipThroughB c $fromJust $getBlock c b2 ) ++ (map (\x -> (b1,x)) $zipThroughB' $ fgFocus $ focus b1 c)
		(ZLast (LastOther (While' _ (b1:b2:_)) ))-> (zipThroughB c $ fromJust$ getBlock c b2) ++ (map (\x -> (b1,x))$zipThroughB' $fgFocus $ focus b1 c)
		(ZLast (LastOther (InitialBranch' bs )))-> concatMap (\x -> zipThroughB c $ fromJust$ getBlock c x) bs
		_ -> []
        --
-- A version that doesn't jump to other blocks
zipThroughB' :: ZBlock a l -> [a]
zipThroughB' b = case zbTail b of 
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
