{-# LANGUAGE DeriveDataTypeable, FlexibleInstances #-}

module RegisterAlloc where 

import Debug.Trace (trace)
import LowIR
import MidIR
import Data.Function (on)
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
import Control.Monad
import Control.Applicative
import Control.Monad.State
import Data.Maybe
import Data.List
import Data.Set (Set, fromList, toList)
import qualified Data.Set as Set
import DataflowAnalysis
import Data.Char (toLower)

type Var = String
data Color = CRAX | CRBX | CRCX | CRDX | CRSP | CRBP | CRSI | CRDI | CR8 | CR9 | CR10 | CR11 | CR12 | CR13 | CR14 | CR15 deriving (Eq, Show, Ord, Enum, Data, Typeable)

data MemLoc = BasePtrOffset Int deriving (Eq, Ord, Show, Data, Typeable)

instance PrettyPrint MemLoc where
    ppr (BasePtrOffset i) = int (i*8) <> lparen <> text "%rbp" <> rparen

instance PrettyPrint Color where
    ppr = text . ('%':) . tail . map toLower . show

allColors = [CRAX .. CR15]

numColors :: Integer
numColors = fromIntegral $ length allColors

-- Should be only a set of two elements.. might fix this to make it
-- required by the type system later if it turns out to matter at all.
type IGEdge a = Set (Set a)
type IGVertex a = Set a

-- An interference graph is a set of vertices and a set of undirected
-- edges between vertices here represented by a set of sets of
-- vertices, all of which should have exactly two elements.  We also
-- assume in the algorithms that no edge goes from a vertex to itself.
data InterferenceGraph a = IG {
    vertices :: (Set (IGVertex a)),
    iEdges :: (Set (IGEdge a)),
    pEdges :: (Set (IGEdge a))
    } deriving (Eq, Show, Ord, Data, Typeable)

instance (Show a, Ord a) => PrettyPrint (InterferenceGraph a) where
    ppr (IG vertices iEdges pEdges) = text "" $$
                         text "Interference Graph ===========================" $$
                         text "Vertices:" <+> hsep (map showSet (toList vertices)) $$ text "" $$
                         text "Interference Edges:" <+> vcat (map id $ 
                                                 map (\(v1:v2:vs) -> lparen <> showSet v1 <> comma <+> showSet v2 <> rparen) $ 
                                                 sort $ 
                                                 map toList $ 
                                                 toList iEdges) $$
                         text "Preference Edges:" <+> vcat (map id $ 
                                                 map (\(v1:v2:vs) -> lparen <> showSet v1 <> comma <+> showSet v2 <> rparen) $ 
                                                 sort $ 
                                                 map toList $ 
                                                 toList pEdges) $$
                         text "==============================================" $$
                         text ""
       where showSet set = lbrace <> withCommas (toList set) <> rbrace
             withCommas = foldl (\acc x -> acc <+> (text . show) x <> comma) (text "")
                        

isVertex :: (Ord a) => IGVertex a -> InterferenceGraph a -> Bool
isVertex v ig = Set.member v $ vertices ig

makeVertex :: (Ord a) => a -> IGVertex a
makeVertex = Set.singleton

emptyIG :: InterferenceGraph a
emptyIG = IG Set.empty Set.empty Set.empty

unionIG :: (Ord a) => InterferenceGraph a -> InterferenceGraph a -> InterferenceGraph a
unionIG ig ig' = IG vertexSet iEdgeSet pEdgeSet
    where vertexSet = Set.union (vertices ig) (vertices ig')
          iEdgeSet = Set.union (iEdges ig) (iEdges ig')
          pEdgeSet = Set.union (pEdges ig) (pEdges ig')

unionIGs :: (Ord a) => [InterferenceGraph a] -> InterferenceGraph a
unionIGs = foldl unionIG emptyIG

makeEdge :: (Ord a) => a -> a -> IGEdge a
makeEdge v v' = fromList $ map makeVertex [v,v']

neighbors :: (Ord a) => IGVertex a -> InterferenceGraph a -> Set (IGVertex a)
neighbors v ig = Set.filter (\v' -> Set.member (fromList [v, v']) edgeSet) $ vertices ig
    where edgeSet = iEdges ig

degree :: (Ord a) => IGVertex a -> InterferenceGraph a -> Integer
degree v ig = fromIntegral $ Set.size $ neighbors v ig

removeVertex :: (Ord a) => IGVertex a -> InterferenceGraph a -> InterferenceGraph a
removeVertex v ig = IG vertices' iEdges' pEdges'
    where vertices' = Set.delete v $ vertices ig
          iEdges' = Set.filter (Set.notMember v) $ iEdges ig
          pEdges' = Set.filter (Set.notMember v) $ pEdges ig

-- Adds an edge, adding the neccessary vertices as well if they don't already exist.
addIEdge :: (Ord a) => IGVertex a -> IGVertex a -> InterferenceGraph a -> InterferenceGraph a
addIEdge v1 v2 ig = IG vertices' iEdges' (pEdges ig)
    where vertices' = Set.union (fromList [v1,v2]) $ vertices ig
          iEdges' = Set.insert (fromList [v1,v2]) $ iEdges ig

-- Adds an edge, adding the neccessary vertices as well if they don't already exist.
addPEdge :: (Ord a) => IGVertex a -> IGVertex a -> InterferenceGraph a -> InterferenceGraph a
addPEdge v1 v2 ig = IG vertices' (iEdges ig) pEdges'
    where vertices' = Set.union (fromList [v1,v2]) $ vertices ig
          pEdges' = Set.insert (fromList [v1,v2]) $ pEdges ig

areNeighbors :: (Ord a) => IGVertex a -> IGVertex a -> InterferenceGraph a -> Bool
areNeighbors v e ig = fromList [v,e] `Set.member` iEdges ig

subsetsOfSize :: (Ord a) => Int -> Set a -> Set (Set a)
subsetsOfSize k xs = fromList $ subsetsOfSize' k (toList xs)

subsetsOfSize' :: (Ord a) => Int -> [a] -> [Set a]
subsetsOfSize' 0 _ = [Set.empty]
subsetsOfSize' n xs = nub $ do
    x <- xs
    nMinusOneSet <- subsetsOfSize' (n-1) (delete x xs)
    return $ Set.insert x nMinusOneSet

discreteOnVertices :: (Ord a) => Set a -> InterferenceGraph a
discreteOnVertices vertices = IG (Set.map makeVertex vertices) Set.empty Set.empty

completeOnVertices :: (Ord a) => Set a -> InterferenceGraph a
completeOnVertices vertices = IG vertexSet iEdges Set.empty
    where iEdges = subsetsOfSize 2 vertexSet
          vertexSet = Set.map makeVertex vertices

addVertex :: (Ord a) => IGVertex a -> InterferenceGraph a -> InterferenceGraph a
addVertex v ig = IG (Set.insert v $ vertices ig) (iEdges ig) (pEdges ig)

-----------------------------------------------------
-- Building Interference graph from liveness analysis
-- This code is too specific and is probably abstracting away to
-- a general fold across any dataflow analysis results.. TODO
-----------------------------------------------------

-- Uses the liveness analysis of a program to build its interference graph for register allocation
buildIGFromMidCfg :: LGraph Statement BranchingStatement -> InterferenceGraph Var
buildIGFromMidCfg cfg = unionIG (discreteOnVertices (allNonArrayVarsForMidCfg cfg)) conflictsIG
    where conflictsIG = foldWithDFR liveVariableAnalysis computeIGfromMidIRNode unionIG emptyIG cfg

computeIGfromMidIRNode :: (Either BranchingStatement Statement, LiveVarState) -> InterferenceGraph Var
computeIGfromMidIRNode (Left l, liveVars) = completeOnVertices $ Set.map varName $ Set.filter (not . isArray) $ liveVars
computeIGfromMidIRNode (Right m, liveVars) = case m of
                Set (Var s) (Loc (Var s')) -> addPEdge (makeVertex s) (makeVertex s') beforePEdges
                _ -> beforePEdges
    where relevantVarNames = Set.map varName $ Set.filter (not . isArray) $ liveVars
          beforePEdges = completeOnVertices relevantVarNames

buildIGFromLowCfg :: LGraph ProtoASM ProtoBranch -> InterferenceGraph Var
buildIGFromLowCfg cfg = unionIG (discreteOnVertices (allNonArrayVarsForLowCfg cfg)) conflictsIG
    where conflictsIG = foldWithDFR lowLVAnalysis computeIGfromLowIRNode unionIG emptyIG cfg

computeIGfromLowIRNode :: (Either ProtoBranch ProtoASM, LiveVarState) -> InterferenceGraph Var
computeIGfromLowIRNode (Left l, liveVars) = completeOnVertices $ Set.map varName $ Set.filter (not . isArray) $ liveVars
computeIGfromLowIRNode (Right m, liveVars) = case m of
                Mov' (Symbol s) (Symbol s') -> addPEdge (makeVertex s) (makeVertex s') beforePEdges
                CMove' (Symbol s) (Symbol s') -> addPEdge (makeVertex s) (makeVertex s') beforePEdges
                CMovne' (Symbol s) (Symbol s') -> addPEdge (makeVertex s) (makeVertex s') beforePEdges
                CMovg' (Symbol s) (Symbol s') -> addPEdge (makeVertex s) (makeVertex s') beforePEdges
                CMovl' (Symbol s) (Symbol s') -> addPEdge (makeVertex s) (makeVertex s') beforePEdges
                CMovge' (Symbol s) (Symbol s') -> addPEdge (makeVertex s) (makeVertex s') beforePEdges
                CMovle' (Symbol s) (Symbol s') -> addPEdge (makeVertex s) (makeVertex s') beforePEdges
                _ -> beforePEdges
    where relevantVarNames = Set.map varName $ Set.filter (not . isArray) $ liveVars
          beforePEdges = completeOnVertices relevantVarNames

------------------------------------------------------------
-- Implement actual register allocation via graph coloring..
------------------------------------------------------------

type Coloring a = M.Map a Color

hasSigDegree :: (Ord a) => IGVertex a -> InterferenceGraph a -> Bool
hasSigDegree v ig@(IG vertices iEdges _) = degree v ig >= numColors

-- Tries to coalesce nodes with a preference edge between them and returns the 
-- coalesced graph along with whether or not anything was changed.
coalesce :: (Ord a) => InterferenceGraph a -> (InterferenceGraph a, Bool)
coalesce ig@(IG vertices iEdges pEdges) = case relevantPEdges of
                                               -- TODO: Should we remove irrelevant pEdges?
                                               [] -> (IG vertices iEdges (fromList validPEdges), False) -- Cant coalesce anything
                                               (e:_) -> (fst $ coalesce $ getNewIG e, True)
    where validPEdges = toList $ Set.filter valid pEdges -- Cant coalesce interfering vertices
          valid pEdge = not $ any (conflicts pEdge) $ toList iEdges
          conflicts pEdge iEdge = (i1 `contains` p1 && i2 `contains` p2) || (i1 `contains` p2 && i2 `contains` p1)
              where (p1:p2:_) = toList pEdge
                    (i1:i2:_) = toList iEdge
                    contains = flip Set.isSubsetOf
          relevantPEdges = filter (\e -> edgeDeg e < numColors) validPEdges
          edgeDeg edge = foldr (+) 0 $ map ((flip degree) ig) (toList edge)
          getVerts e = Set.insert (Set.unions (toList e)) $ Set.difference vertices e
          getIEdges e = Set.map (setReplace e (Set.unions (toList e))) iEdges
          getPEdges e = Set.delete e pEdges
          getNewIG e = IG (getVerts e) (getIEdges e) (getPEdges e)


insertAllWithKey :: (Ord k) => Set k -> a -> M.Map k a -> M.Map k a
insertAllWithKey keys val = compose $ map (\k -> M.insert k val) (toList keys)

defAllocateRegisters :: (RegisterAllocatable b) => b -> Coloring Var
defAllocateRegisters = allocateRegisters (const 0)

class RegisterAllocatable a where
    computeInterferenceGraph :: a -> InterferenceGraph Var
    updateForSpills :: [(IGVertex Var, MemLoc)] -> a -> a

instance RegisterAllocatable (LGraph Statement BranchingStatement) where
    computeInterferenceGraph = buildIGFromMidCfg
    updateForSpills _ = error "not yet implemented"

instance RegisterAllocatable (LGraph ProtoASM ProtoBranch) where
    computeInterferenceGraph = buildIGFromLowCfg
    updateForSpills spilled graph =  res
        where flattener (xs, y) = zip xs (repeat y)
              spilled' = concatMap (flattener . mapFst toList) spilled
              res = foldl updateForSpill graph $ spilled'

updateForSpill :: LGraph ProtoASM ProtoBranch -> (Var, MemLoc) -> LGraph ProtoASM ProtoBranch
updateForSpill graph (spillVar, BasePtrOffset i) = trace ("updateForSpill called with var: " ++ spillVar) $ res
    where mMap = \_ asm -> case asm `usesVariable` spillVar of
                True -> [Mov' (Stack i) (Symbol spillVar), asm, Mov' (Symbol spillVar) (Stack i)]
                False -> [asm]
          lMap _ LastExit = (([], []), LastExit)
          lMap _ zl@(LastOther branch) = case branch `usesVariable` spillVar of
              True -> (([],[Mov' (Stack i) (Symbol spillVar)]), zl) -- Fix me yada yada
              False -> (([],[]), zl)
          res = mapLGraphNodes mMap lMap graph
          


allocateRegisters :: (Ord a, RegisterAllocatable b) => (IGVertex Var -> a) -> b -> Coloring Var
allocateRegisters spillHeuristic cfg = case coloringOrSpills of
            Right coloring -> coloring
            Left spills -> allocateRegisters spillHeuristic (updateForSpills spills cfg)
    where initialIG = computeInterferenceGraph cfg
          (simpleIG, vertexStack) = simplify spillHeuristic initialIG
          coloringOrSpills = select (iEdges simpleIG) vertexStack
          
select :: (Ord a, Show a) => Set (IGEdge a) -> [IGVertex a] -> Either [(IGVertex a, MemLoc)] (Coloring a)
select iEdges vertexStack = fst $ runState (select' initialGraph M.empty) (vertexStack, [])
    where initialGraph = IG Set.empty iEdges Set.empty

select' :: (Ord a, Show a) => InterferenceGraph a -> Coloring a -> State ([IGVertex a], [(IGVertex a, MemLoc)]) (Either [(IGVertex a, MemLoc)] (Coloring a))
select' graph colorMap = do
    mbVertex <- popLeft
    spilled <- liftM snd get
    case mbVertex of
        Nothing -> return $ if null spilled then Right colorMap else Left spilled
        Just v -> let neighborColors = catMaybes $ 
                                       map ((flip M.lookup) colorMap) $
                                       concat $ map toList $ toList $
                                       neighbors v graph
                      availColors = allColors \\ neighborColors 
                      -- TODO: Remove trace
                      graph' = trace (show (v, availColors, length availColors, degree v graph)) $ addVertex v graph
                      BasePtrOffset curBPMax = if null spilled then BasePtrOffset 1 else maximum $ map snd spilled
                      in
                  if null availColors then
                                      pushRight (v, BasePtrOffset (curBPMax+1)) >> select' graph' colorMap
                                      else
                                      select' graph' (insertAllWithKey v (head availColors) colorMap)

setReplace :: (Ord a) => Set a -> a -> Set a -> Set a
setReplace olds new set = Set.map replaceFunc set
    where replaceFunc x = case x `Set.member` olds of
                              True -> new
                              False -> x

defSimplify :: (Ord a) => InterferenceGraph a -> (InterferenceGraph a, [IGVertex a])
defSimplify = simplify (const 1)
    
simplify spillHeuristic ig = runState (simplify' spillHeuristic ig) []

-- TODO: Optimize this later if you have time..
simplify' :: (Ord a, Ord b) => (IGVertex a -> b) -> InterferenceGraph a -> State [IGVertex a] (InterferenceGraph a)
simplify' spillHeuristic ig@(IG vertices iEdges pEdges) = case Set.null vertices of
    -- If empty.. nothing to do.. proceed to coloring
    True -> return ig
    -- Otherwise.. remove chosen vertex and do it again
    False -> if isSpill then do
            let (coalescedIG, anyChanges) = coalesce ig
            if anyChanges then
                          simplify' spillHeuristic coalescedIG
                          else do
                              push colorNext
                              simplify' spillHeuristic (removeFromVertexSet colorNext ig)
        else do
            push colorNext
            simplify' spillHeuristic (removeFromVertexSet colorNext ig)
    where canSimplify v = not $ (hasSigDegree v ig || isMoveRelated v) -- TODO: Also ensure not move related
          removeFromVertexSet v (IG vs ies pes) = IG (Set.delete v vs) ies pes
          isMoveRelated v = any (Set.member v) $ toList pEdges
          simplifiable = Set.filter canSimplify vertices
          (colorNext, isSpill) = case Set.null simplifiable of -- Any candidates for simplification?
              -- Yes? Pick an arbitrary one
              False -> (head $ toList simplifiable, False)
              -- No? Choose the one with the worst spillHeurstic and it is a potential
              -- spill candidate
              True -> (minimumBy (compare `on` spillHeuristic) $ toList vertices, True)

