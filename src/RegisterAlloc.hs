{-# LANGUAGE DeriveDataTypeable #-}

module RegisterAlloc where 

import MidIR
import Data.List (sort)
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
import Control.Monad
import Control.Applicative
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

instance (Show a, Ord a) => PrettyPrint (InterferenceGraph a) where
    ppr (IG vSet eSet) = text "" $$
                         text "Interference Graph ===========================" $$
                         text "Vertices:" <+> hsep (map (text . show) (Set.toList vSet)) $$ text "" $$
                         text "Edges:" <+> vcat (map text $ 
                                                 map (\(v1:v2:vs) -> "(" ++ show v1 ++ ", " ++ show v2 ++ ")") $ 
                                                 sort $ 
                                                 map Set.toList $ 
                                                 Set.toList eSet) $$
                         text "==============================================" $$
                         text ""
                        

isVertex :: (Ord a) => a -> InterferenceGraph a -> Bool
isVertex v ig = Set.member v $ vertices ig

emptyIG :: InterferenceGraph a
emptyIG = IG Set.empty Set.empty

unionIG :: (Ord a) => InterferenceGraph a -> InterferenceGraph a -> InterferenceGraph a
unionIG ig ig' = IG vertexSet edgeSet
    where vertexSet = Set.union (vertices ig) (vertices ig')
          edgeSet = Set.union (edges ig) (edges ig')

unionIGs :: (Ord a) => [InterferenceGraph a] -> InterferenceGraph a
unionIGs = foldl unionIG emptyIG

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

discreteOnVertices :: (Ord a) => Set a -> InterferenceGraph a
discreteOnVertices vertices = IG vertices Set.empty

completeOnVertices :: (Ord a) => Set a -> InterferenceGraph a
completeOnVertices vertices = IG vertices edges
    where edges = subsetsOfSize 2 vertices

addVertex :: (Ord a) => a -> InterferenceGraph a -> InterferenceGraph a
addVertex v ig = IG (Set.insert v $ vertices ig) (edges ig)

-----------------------------------------------------
-- Building Interference graph from liveness analysis
-- This code is too specific and is probably abstracting away to
-- a general fold across any dataflow analysis results.. TODO
-----------------------------------------------------

-- Uses the liveness analysis of a program to build its interference graph for register allocation
buildInterferenceGraph :: LGraph Statement BranchingStatement -> InterferenceGraph Var

buildInterferenceGraph lgraph = unionIG (discreteOnVertices $ allNonArrayVariables lgraph) conflictsGraph
    where DFR _ blockLivenessMap = runAnalysis liveVariableAnalysis lgraph
          -- conflictsGraph only includes those variables who conflicted with some other variable at some point
          -- we union this with "discreteOnVertices $ allNonArrayVariables lgraph" to ensure that non-conflicting
          -- variables are assigned registers too.
          conflictsGraph = unionIGs $ map (interferenceFromBlock blockLivenessMap) $ postorderDFS lgraph

interferenceFromBlock :: M.Map BlockId LiveVarState -> Block Statement BranchingStatement -> InterferenceGraph Var
interferenceFromBlock blockStates blk@(Block bid _) = fst $ runState results blkOutState
    where blkOutState = case M.lookup bid blockStates of
                    Nothing -> error "Cant find block in results.  liveness analysis must have failed"
                    Just b -> b
          foldingF acc stmt = do
              liveVars <- get
              put $ liveVarUpdateM stmt liveVars 
              let relevantLiveVarNames = Set.map varName $ Set.filter (not . isArray) $ liveVars
              return $ unionIG acc (completeOnVertices relevantLiveVarNames)
          results = foldM foldingF emptyIG (reverse $ blockMiddles blk)

subsetsOfSize :: (Ord a) => Int -> Set a -> Set (Set a)
subsetsOfSize k xs = Set.filter (\as -> Set.size as == k) $ Set.fromList $ map Set.fromList powerset
    where powerset = filterM (const [True, False]) $ Set.toList xs






