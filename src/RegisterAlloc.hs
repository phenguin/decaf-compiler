{-# LANGUAGE DeriveDataTypeable #-}

module RegisterAlloc where 

import MidIR
import Util
import qualified Data.Map as M
import ControlFlowGraph
import CFGConcrete
import CFGConstruct
import Data.Data
import Data.Typeable
import Data.Generics
import System.IO.Unsafe
import PrettyPrint
import Text.PrettyPrint.HughesPJ hiding (Str)
import Debug.Trace
import Control.Monad.State
import Data.Maybe
import Data.List
import Data.Set (Set, fromList)
import qualified Data.Set as Set
import DataflowAnalysis

type Var = String
type Color = Integer

-- Should be only a set of two elements.. might fix this to make it
-- required by the type system later if it turns out to matter at all.
type Edge a = Set a

-- An interference graph is a set of vertices and a set of undirected
-- edges between vertices here represented by a set of sets of
-- vertices, all of which should have exactly two elements.  We also
-- assume in the algorithms that no edge goes from a vertex to itself.
data InterferenceGraph a = IG {
    vertices :: (Set a),
    edges :: (Set (Edge a))
    } deriving (Eq, Show, Ord, Data, Typeable)

isVertex :: (Ord a) => a -> InterferenceGraph a -> Bool
isVertex v ig = Set.member v $ vertices ig

emptyIG :: InterferenceGraph a
emptyIG = IG Set.empty Set.empty

unionIGs :: (Ord a) => InterferenceGraph a -> InterferenceGraph a -> InterferenceGraph a
unionIGs ig ig' = IG vertexSet edgeSet
    where vertexSet = Set.union (vertices ig) (vertices ig')
          edgeSet = Set.union (edges ig) (edges ig')

vertexNeighbors :: (Ord a) => a -> InterferenceGraph a -> Set a
vertexNeighbors v ig = Set.filter (\v' -> Set.member (fromList [v, v']) edgeSet) $ vertices ig
    where edgeSet = edges ig

vertexDegree :: (Ord a) => a -> InterferenceGraph a -> Integer
vertexDegree v ig = fromIntegral $ Set.size $ vertexNeighbors v ig

removeVertex :: (Ord a) => a -> InterferenceGraph a -> InterferenceGraph a
removeVertex v ig = IG newVertexSet newEdgeSet
    where newVertexSet = Set.delete v $ vertices ig
          newEdgeSet = Set.filter (Set.notMember v) $ edges ig

-- Adds an edge, adding the neccessary vertices as well if they don't already exist.
addEdge :: (Ord a) => a -> a -> InterferenceGraph a -> InterferenceGraph a
addEdge v1 v2 ig = IG vertexSet edgeSet
    where vertexSet = Set.union (fromList [v1,v2]) $ vertices ig
          edgeSet = Set.insert (fromList [v1,v2]) $ edges ig

addVertex :: (Ord a) => a -> InterferenceGraph a -> InterferenceGraph a
addVertex v ig = IG (Set.insert v $ vertices ig) (edges ig)

-----------------------------------------------------
-- Building Interference graph from liveness analysis
-----------------------------------------------------

buildInterferenceGraph :: (PrettyPrint l, LastNode l) => 
    LGraph Statement l -> InterferenceGraph Var
buildInterferenceGraph lgraph = undefined
    where DFR _ blockLivenessMap = runAnalysis liveVariableAnalysis lgraph



