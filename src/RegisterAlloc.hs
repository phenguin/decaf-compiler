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
import qualified Transforms
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
data Color = CRCX | CRDX | CRSI | CRDI | CR8 | CR9 | CRSP | CRBP | CRAX | CRBX | CR10 | CR11 | CR12 | CR13 | CR14 | CR15 deriving (Eq, Show, Ord, Enum, Data, Typeable)

allColors = [CRBX .. CR15]

numColors :: Integer
numColors = fromIntegral $ length allColors

colorToValue :: Color -> Value
colorToValue CRAX = RAX
colorToValue CRBX = RBX
colorToValue CRCX = RCX
colorToValue CRDX = RDX
colorToValue CRSP = RSP
colorToValue CRBP = RBP
colorToValue CRSI = RSI
colorToValue CRDI = RDI
colorToValue CR8 = R8
colorToValue CR9 = R9
colorToValue CR10 = R10
colorToValue CR11 = R11
colorToValue CR12 = R12
colorToValue CR13 = R13
colorToValue CR14 = R14
colorToValue CR15= R15

data MemLoc = BasePtrOffset Int deriving (Eq, Ord, Show, Data, Typeable)

instance PrettyPrint MemLoc where
    ppr (BasePtrOffset i) = int (i*8) <> lparen <> text "%rbp" <> rparen

instance PrettyPrint Color where
    ppr = text . ('%':) . tail . map toLower . show

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

instance (Ord a, PrettyPrint a) => PrettyPrint (InterferenceGraph a) where
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
             withCommas = foldl (\acc x -> acc <+> ppr x <> comma) (text "")
                        

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

-- Note: These is currently computing the inference graph in the wrong way so it shouldn't be used...
buildIGFromMidCfg :: LGraph Statement BranchingStatement -> InterferenceGraph VarMarker
buildIGFromMidCfg cfg = unionIG (discreteOnVertices (allNonArrayVarsForMidCfg cfg)) conflictsIG
    where conflictsIG = foldWithDFR liveVariableAnalysis computeIGfromMidIRNode unionIG emptyIG cfg

computeIGfromMidIRNode :: (Either BranchingStatement Statement, LiveVarState) -> InterferenceGraph VarMarker
computeIGfromMidIRNode (Left l, liveVars) = completeOnVertices $ Set.filter (not . isArray) $ liveVars
computeIGfromMidIRNode (Right m, liveVars) = case m of
                Set v (Loc v') -> let vm = varToVarMarker v
                                      vm' = varToVarMarker v' in
                                  if not $ (isArray vm || isArray vm') then
                                     addPEdge (makeVertex vm) (makeVertex vm') beforePEdges
                                     else
                                     beforePEdges
                _ -> beforePEdges
    where relevantVarNames = Set.filter (not . isArray) $ liveVars
          beforePEdges = completeOnVertices relevantVarNames

buildIGFromLowCfg :: LGraph ProtoASM ProtoBranch -> InterferenceGraph VarMarker
buildIGFromLowCfg cfg = unionIG (discreteOnVertices (allNonArrayVarsForLowCfg cfg)) conflictsIG
    where conflictsIG = foldWithDFR lowLVAnalysis computeIGfromLowIRNode unionIG emptyIG cfg

computeIGfromLowIRNode :: (Either ProtoBranch ProtoASM, LiveVarState) -> InterferenceGraph VarMarker
computeIGfromLowIRNode (Left l, liveVars) = case l of
        If' asms bids -> unionIGs $ map middlesMapF asms
        While' asms bids -> unionIGs $ map middlesMapF asms
        -- TODO: Check on how structure relates to for loop semantics
        For' v asms1 asms2 asms3 bids -> unionIGs $ map middlesMapF (concat [asms1, asms2, asms3])
        Parafor' v asms1 asms2 asms3 bids -> unionIGs $ map middlesMapF (concat [asms1, asms2, asms3])
        InitialBranch' bids -> emptyIG
        Jump' _ -> emptyIG
        Nil -> emptyIG
    where middlesMapF = \m -> computeIGfromLowIRNode (Right m, liveVars)

computeIGfromLowIRNode (Right m, liveVars) = case m of
                Mov' v v' -> addPEdgeOrId v v' $ beforePEdges v' (Just v)
                CMove' v v' -> addPEdgeOrId v v' $ beforePEdges v' (Just v)
                CMovne' v v' -> addPEdgeOrId v v' $ beforePEdges v' (Just v)
                CMovg' v v' -> addPEdgeOrId v v' $ beforePEdges v' (Just v)
                CMovl' v v' -> addPEdgeOrId v v' $ beforePEdges v' (Just v)
                CMovge' v v' -> addPEdgeOrId v v' $ beforePEdges v' (Just v)
                CMovle' v v' -> addPEdgeOrId v v' $ beforePEdges v' (Just v)
                Neg' v ->  beforePEdges v Nothing
                And' _ v ->  beforePEdges v Nothing
                Or' _ v ->  beforePEdges v Nothing
                Add' _ v ->  beforePEdges v Nothing
                Sub' _ v ->  beforePEdges v Nothing
                Mul' _ v ->  beforePEdges v Nothing
                -- TODO: Needs to interfere with RAX and RDX precolored regs.
                Div' v -> beforePEdges v Nothing
                Not' v -> beforePEdges v Nothing
                Pop' v -> beforePEdges v Nothing
                _ -> emptyIG
    where relevantVarNames = Set.filter (not . isArray) $ liveVars
          beforePEdges defV maybeExclude = foldr (uncurry addIEdge) (discreteOnVertices relevantVarNames) $ toList (interfering defV maybeExclude)
          interfering (Scoped scp (Symbol s)) maybeExclude = case maybeExclude of
                    Just (Scoped scp'' (Symbol s'')) -> Set.map (\vm' -> (makeVertex vm, makeVertex vm')) $ 
                                                             Set.filter (/=(VarMarker s'' Transforms.Single scp'')) $
                                                             Set.filter (/=vm) $
                                                             relevantVarNames
                    _ -> Set.map (\vm' ->  (makeVertex vm, makeVertex vm')) $
                                                           Set.filter (/=vm) $ 
                                                           relevantVarNames
                where vm = VarMarker s Transforms.Single scp
          interfering _ _ = Set.empty
          addPEdgeOrId (Scoped scp (Symbol s)) (Scoped scp' (Symbol s')) = addPEdge (makeVertex (VarMarker s Transforms.Single scp))
                                                                                    (makeVertex (VarMarker s' Transforms.Single scp'))
          addPEdgeOrId _ _ = id

------------------------------------------------------------
-- Implement actual register allocation via graph coloring..
------------------------------------------------------------

type Coloring a = M.Map a Color

hasSigDegree :: (Ord a) => IGVertex a -> InterferenceGraph a -> Bool
hasSigDegree v ig@(IG vertices iEdges _) = degree v ig >= numColors

-- Tries to coalesce nodes with a preference edge between them and returns the 
-- coalesced graph along with whether or not anything was changed.
coalesce :: (Ord a, PrettyPrint a) => InterferenceGraph a -> (InterferenceGraph a, Bool)
coalesce ig@(IG vertices iEdges pEdges) = case relevantPEdges of
                                               -- TODO: Should we remove irrelevant pEdges?
                                               [] -> (IG vertices iEdges (fromList validPEdges), False) -- Cant coalesce anything
                                               (e:_) -> (fst $ coalesce $ getNewIG e, True)
    where validPEdges = toList $ Set.filter valid pEdges -- Cant coalesce interfering vertices
          valid pEdge = not $ any (conflicts pEdge) $ toList iEdges
          conflicts pEdge iEdge = (i1 `contains` p1 && i2 `contains` p2) || (i1 `contains` p2 && i2 `contains` p1)
              where [p1,p2] = toList pEdge
                    [i1,i2] = toList iEdge
                    contains = flip Set.isSubsetOf
          relevantPEdges = filter (\e -> edgeDeg e < numColors) validPEdges
          edgeDeg edge = foldr (+) 0 $ map ((flip degree) ig) (toList edge)
          getVerts e = Set.insert (Set.unions (toList e)) $ Set.difference vertices e
          getIEdges e = Set.map (setReplace e (Set.unions (toList e))) iEdges
          getPEdges e = Set.union inheritedPEdges $ Set.delete e pEdges
            where inheritedEdgesFor v = if all (\v' -> (fromList [v, v']) `Set.member` pEdges) endpts
                                          then
                                          Set.singleton $ fromList [v, (Set.unions (toList e))]
                                          else
                                          Set.empty
                  inheritedPEdges = Set.unions $ map inheritedEdgesFor $ toList (getVerts e)
                  endpts = toList e
          getNewIG e = IG (getVerts e) (getIEdges e) (getPEdges e)


insertAllWithKey :: (Ord k) => Set k -> a -> M.Map k a -> M.Map k a
insertAllWithKey keys val = compose $ map (\k -> M.insert k val) (toList keys)

-- Should play with this..
vmSpillHeuristic ig vmSet = (-1 * totalDegree, maxNesting, totalNesting )
    where vms = toList vmSet
          vmNesting = length . varScope
          maxNesting = maximum $ map vmNesting vms
          totalNesting = sum $ map vmNesting vms
          totalDegree = sum $ map ((flip degree) ig) $ map makeVertex vms


defAllocateRegisters :: (PrettyPrint b, RegisterAllocatable b) => b -> (Coloring VarMarker, b)
defAllocateRegisters = allocateRegisters vmSpillHeuristic

class RegisterAllocatable a where
    computeInterferenceGraph :: a -> InterferenceGraph VarMarker
    updateForSpills :: [(IGVertex VarMarker, MemLoc)] -> a -> a

instance RegisterAllocatable (LGraph Statement BranchingStatement) where
    computeInterferenceGraph = buildIGFromMidCfg
    updateForSpills _ = error "not yet implemented"

instance RegisterAllocatable (LGraph ProtoASM ProtoBranch) where
    computeInterferenceGraph = buildIGFromLowCfg
    updateForSpills spilled graph = fst $ runState resM (0,0)
        where flattener (xs, y) = zip xs (repeat y)
              spilled' = concatMap (flattener . mapFst toList) spilled
              foldF graph spillMemPair = do
                  modify $ mapFst (subtract 1)
                  updateForSpill graph spillMemPair
              resM = foldM foldF graph $ spilled'

mkSpillTemp :: VarMarker -> Int -> Value
mkSpillTemp (VarMarker name _ scp) i = Scoped [Temp] (Symbol $ vmStr ++ "_" ++ show i)
    where scpStr (Global:scps) = "global_" ++ scpStr scps
          scpStr (Temp:scps) = "temp_" ++ scpStr scps
          scpStr ((Func s):scps) = "func[" ++ s ++ "]_" ++ scpStr scps
          scpStr ((Loop s):scps) = "loop[" ++ s ++ "]_" ++ scpStr scps
          scpStr [] = ""
          vmStr = scpStr scp ++ name

updateForSpill :: LGraph ProtoASM ProtoBranch -> (VarMarker, MemLoc) -> State (Int,Int) (LGraph ProtoASM ProtoBranch)
updateForSpill graph (spillVM, BasePtrOffset i) = res
    where isDec (Dec' _) = True
          isDec _ = False
          mMapM = \_ asm -> case asm `usesVariable` spillVM && (not . isDec) asm of
                True -> do
                    (i,j) <- get
                    modify $ mapSnd (+1)
                    let newTempVar = mkSpillTemp spillVM j
                        memLocation = Stack (8*i)
                        asm' = replaceValinStmt spillVM newTempVar asm
                    return [Mov' memLocation newTempVar, asm', Mov' newTempVar memLocation]
                False -> if isDec asm then return [] else return [asm]
          lMapM _ LastExit = return (([], []), LastExit)
          -- TODO: Fix me.. this is wrong, need to reload after branch
          lMapM _ zl@(LastOther branch) = case branch `usesVariable` spillVM of
              True -> do
                  (i,j) <- get
                  modify $ mapSnd (+1)
                  let newTempVar = mkSpillTemp spillVM j
                      memLocation = Stack (8*i)
                      branch' = replaceValinStmt spillVM newTempVar branch
                  return (([],[Mov' memLocation newTempVar]), LastOther branch')
              False -> return (([],[]), zl)
          res = mapLGraphNodesM mMapM lMapM graph

keysByValue :: (Ord k, Eq a) => M.Map k a -> [Set k]
keysByValue lkp = map (fromList . keysWithVal) $ M.elems lkp
    where keysWithVal a = filter (\k -> M.lookup k lkp == Just a) keys
          keys = M.keys lkp
          
removeRedundantMoves :: Coloring VarMarker -> LGraph ProtoASM ProtoBranch -> LGraph ProtoASM ProtoBranch
removeRedundantMoves coloring graph = mapLGraphNodes mMap lMap graph
    where redundant v v' = isSymbol v && isSymbol v' && (any (Set.isSubsetOf (valsToVMSet [v,v'])) $ vertices)
          vertices = keysByValue coloring
          isSymbol (Scoped _ (Symbol _)) = True
          isSymbol _ = False
          mMap bid stmt = case stmt of
              Mov' v v' -> if redundant v v' then [] else  [stmt]
              CMove' v v' -> if redundant v v' then [] else  [stmt]
              CMovne' v v' -> if redundant v v' then [] else [stmt]
              CMovl' v v' -> if redundant v v' then [] else [stmt]
              CMovg' v v' -> if redundant v v' then [] else [stmt]
              CMovle' v v' -> if redundant v v' then [] else [stmt]
              CMovge' v v' -> if redundant v v' then [] else [stmt]
              _ -> [stmt]
          lMap bid zl = (([],[]), zl)

allocateRegisters :: (Ord a, RegisterAllocatable b, PrettyPrint b) => 
    (InterferenceGraph VarMarker -> IGVertex VarMarker -> a) -> b -> (Coloring VarMarker, b)
allocateRegisters spillHeuristic cfg = case coloringOrSpills of
            Right coloring -> (coloring, cfg)
            Left spills -> allocateRegisters spillHeuristic (updateForSpills spills cfg)
    where initialIG = computeInterferenceGraph cfg
          (simpleIG, vertexStack) = simplify spillHeuristic initialIG
          coloringOrSpills = select (iEdges simpleIG) vertexStack
          
select :: (Ord a, PrettyPrint a, Show a) => Set (IGEdge a) -> [IGVertex a] -> Either [(IGVertex a, MemLoc)] (Coloring a)
select iEdges vertexStack = fst $ runState (select' initialGraph M.empty) (vertexStack, [])
    where initialGraph = IG Set.empty iEdges Set.empty

select' :: (Ord a, PrettyPrint a, Show a) => InterferenceGraph a -> Coloring a -> State ([IGVertex a], [(IGVertex a, MemLoc)]) (Either [(IGVertex a, MemLoc)] (Coloring a))
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
                      graph' = addVertex v graph
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

defSimplify :: (Ord a, PrettyPrint a) => InterferenceGraph a -> (InterferenceGraph a, [IGVertex a])
defSimplify = simplify ((const . const) 1)
    
simplify spillHeuristic ig = runState (simplify' spillHeuristic ig) []

-- TODO: Optimize this later if you have time..
simplify' :: (Ord a, Ord b, PrettyPrint a) => (InterferenceGraph a -> IGVertex a -> b) -> InterferenceGraph a -> State [IGVertex a] (InterferenceGraph a)
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
              True -> (minimumBy (compare `on` (spillHeuristic ig)) $ toList vertices, True)

-- ApplyNodeColor top down on the whole lgraph
applyColoring :: Coloring VarMarker -> LGraph ProtoASM ProtoBranch -> LGraph ProtoASM ProtoBranch
applyColoring coloring = everywhere' (mkT (applyNodeColor coloring))

-- This is hideous.. but I'm tired and dont feel like writing it nicer
applyNodeColor :: Coloring VarMarker -> Value -> Value
applyNodeColor coloring val = result
    where maybeVarMarker = case toList (valToVMSet val) of
                [vm] -> Just vm
                _ -> Nothing
          color vm = case M.lookup vm coloring of
                       Nothing -> Nothing
                       Just c -> Just c
          result = case maybeVarMarker >>= color of
                     Nothing -> val
                     Just c -> colorToValue c

doRegisterAllocation :: LGraph ProtoASM ProtoBranch -> LGraph ProtoASM ProtoBranch
doRegisterAllocation lgraph = coloredGraph
    where (coloring, finalGraph) = allocateRegisters vmSpillHeuristic lgraph
          coloring' = M.filterWithKey (\k a -> (not . isArray) k) coloring
          lgraph' = trace (pPrint finalGraph ++ "\n" ++ pPrint coloring') $ removeRedundantMoves coloring finalGraph
          coloredGraph = applyColoring coloring' lgraph'

