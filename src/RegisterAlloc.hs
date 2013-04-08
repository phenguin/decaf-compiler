module RegisterAlloc where 

import Optimization
import qualified Data.Map as M
import ControlFlowGraph
import CFGConstruct
import CFGConcrete
import CodeGeneration 
import PrettyPrint
import Text.PrettyPrint.HughesPJ hiding (Str)
import Debug.Trace
import Control.Monad.State
import LowIR
import Data.IORef
import System.IO.Unsafe



type StringState = M.Map String String
--insert = M.insert

lowIRtoAsm lowir = do
	let zcfg = focus (lgEntry lowir) lowir
	let strSt = M.empty
	let strlist = unsafePerformIO $ newIORef []
	let out = graftBlocks lowir
	let cds = findAllStrings zcfg
	putStrLn $ show $ map getString cds 
	return out



graftBlocks cfg = mapLGraphNodes ( values ) (\ _ x -> ([],x)) cfg
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


findAllStrings zcfg = do 
		let blocks = postorderDFS $ unfocus zcfg
		concat $ harvestStrings blocks
	where 	
		harvestStrings (b:blks) = (map (strings.values) (zipThroughB $ unzipB b)) ++ (harvestStrings blks)
		harvestStrings _ = []
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
			(Not'  v)	-> 	[v] 
			(Ret'  v)	->	[v]
			(Call' _)   	->	[]
			(Str' v)	-> 	[v]
			(Cmp' v1 v2)	-> 	[]
			(Je' _)		->	[]
			(Jmp' _)	->	[]
			(Push' v)	->	[v]
			(Pop' v)	->	[v]
		zipThroughB b = case zbTail b of 
					(ZTail m _) -> m:(zipThroughB (nextEdge b))
					_ -> []
						
		strings = filter isString 
	        isString (EvilString str) = True 
	        isString _ 		  = False 

