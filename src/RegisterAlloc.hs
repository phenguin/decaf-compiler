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
import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

unorderedPairs :: (Eq a, Ord a) => [a] -> Set (Set a)
unorderedPairs xs = Set.fromList $ do
    x <- xs
    y <- delete x $ nub xs
    return $ Set.fromList [x,y]
