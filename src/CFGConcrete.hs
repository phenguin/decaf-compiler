{-# LANGUAGE DeriveDataTypeable #-}
module CFGConcrete where

import qualified Data.Map as M
import Data.Data
import Data.Typeable
import Debug.Trace (trace)
import PrettyPrint
import Data.Set (Set)
import Data.Maybe (fromJust, isJust)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

-- Implement control flow graph based off of GHCs own implementation
-- and the paper "An Applicative Control Flow Graph based on Huet's Zipper"

newtype BlockId = BID { getStr :: String } deriving (Show, Eq, Ord, Data, Typeable)

type BlockSet = Set BlockId
emptyBlockSet = Set.empty
insertBlockSet = Set.insert
singleBlockSet = Set.singleton
elemBlockSet = Set.member

type BlockLookup m l = M.Map BlockId (Block m l)

-- Wrappers around Data.Map functions for ease of reading
mapBlocks = M.map
insertBlock = M.insert
listBlocks = M.elems
removeBlock = M.delete
lookupBlock = M.lookup
emptyBlockLookup = M.empty
mergeBlockLookups :: BlockLookup m l -> BlockLookup m l -> BlockLookup m l
mergeBlockLookups = (M.union)

newtype SuccBlocks = SuccBlocks { getSuccBlocks :: [BlockId] } deriving (Show, Eq, Ord)

instance PrettyPrint SuccBlocks where
    ppr (SuccBlocks bs) = text "<End Block>" $$ text "Branch Targets:" <+> (hsep $ map ppr bs) $$ text ""

data ZLast l = LastExit | LastOther l deriving (Show, Eq, Data, Typeable)

data ZHead m = ZFirst BlockId
             | ZHead (ZHead m) m deriving (Show, Eq, Data, Typeable)

data ZTail m l = ZLast (ZLast l)
             | ZTail m (ZTail m l) deriving (Show, Eq, Data, Typeable)

data Block m l = Block { bId :: BlockId,
                         bTail :: ZTail m l } deriving (Show, Data, Typeable)

instance Eq (Block m l) where
    (Block bid1 _) == (Block bid2 _) = bid1 == bid2

instance Ord (Block m l) where
    (Block bid1 _) `compare` (Block bid2 _) = bid1 `compare` bid2

data ZBlock m l = ZBlock { zbHead :: ZHead m, 
                         zbTail :: ZTail m l } deriving (Show, Eq, Data, Typeable)

data Graph m l = Graph { gEntry :: ZTail m l,
                   gBlocks :: BlockLookup m l } deriving (Show, Eq, Data, Typeable)

data LGraph m l = LGraph { lgEntry :: BlockId,
                            lgBlocks :: BlockLookup m l } deriving (Show, Eq, Data, Typeable)

data ZGraph m l = ZGraph { fgEntry :: BlockId,
                            fgFocus :: ZBlock m l, 
                            fgBlocks :: BlockLookup m l } deriving (Show, Eq, Data, Typeable)

class HavingZLast a where
    getZLast :: (a l) -> ZLast l

class HavingBlockId a where
    getBlockId :: a -> BlockId

class HavingSuccessors l where
    succs :: l -> [BlockId]
    foldSuccs :: (BlockId -> a -> a) -> l -> a -> a
    foldSuccs add l z = foldr add z $ succs l

class (HavingSuccessors l) => LastNode l where
    mkBranchNode :: BlockId -> l
    isBranchNode :: l -> Bool

instance LastNode SuccBlocks where
    mkBranchNode x = SuccBlocks [x]
    isBranchNode (SuccBlocks xs) = case xs of
        [x] -> True
        _ -> False

instance HavingBlockId (ZHead m) where
    getBlockId (ZFirst bid) = bid
    getBlockId (ZHead h m) = getBlockId h

instance HavingBlockId (Block m l) where
    getBlockId (Block bid _) = bid

instance HavingBlockId (ZBlock m l) where
    getBlockId (ZBlock h _) = getBlockId h

instance HavingZLast (ZTail m) where
    getZLast (ZTail _ t) = getZLast t
    getZLast (ZLast l) = l

instance HavingZLast (Block m) where
    getZLast (Block _ tl) = getZLast tl

instance HavingZLast (ZBlock m) where
    getZLast (ZBlock _ tl) = getZLast tl

instance HavingSuccessors l => HavingSuccessors (ZLast l) where
    succs LastExit = []
    succs (LastOther x) = succs x

instance HavingSuccessors l => HavingSuccessors (ZTail m l) where
    succs zt = succs $ getZLast zt

instance HavingSuccessors l => HavingSuccessors (Block m l) where
    succs (Block _ ztail) = succs ztail

instance HavingSuccessors l => HavingSuccessors (ZBlock m l) where
    succs zb = succs $ zipB zb

instance HavingSuccessors SuccBlocks where
    succs = getSuccBlocks

-- Utility functions

listToZTail :: (HavingSuccessors l) => [m] -> Maybe l -> ZTail m l
listToZTail [] Nothing = ZLast LastExit
listToZTail [] (Just l) = ZLast (LastOther l)
listToZTail (m:ms) ml = ZTail m (listToZTail ms ml)

listToBlock bid ms ml = (\zt -> Block bid zt) $ listToZTail ms ml

-- Block manipulations
zipB :: ZBlock m l -> Block m l
unzipB :: Block m l -> ZBlock m l
unzipToEndB :: Block m l -> ZBlock m l
htToBlock :: ZHead m -> ZTail m l -> Block m l
htToLast :: ZHead m -> ZTail m l -> (ZHead m, ZTail m l)

htToBlock (ZFirst bid) t = Block bid t
htToBlock (ZHead h m) t = htToBlock h (ZTail m t)

htToLast hd (ZLast l) = (hd, ZLast l)
htToLast hd (ZTail m t) = htToLast (ZHead hd m) t

unzipB (Block bid t) = ZBlock (ZFirst bid) t

unzipToEndB (Block bid t) = ZBlock h t
    where (h, t) = htToLast (ZFirst bid) t

zipB (ZBlock h t) = htToBlock h t

-- Block construction
initBlock :: BlockId -> Block m l
initBlock bid = Block bid (ZLast LastExit)

-- ZBlock Movement
nextEdge :: ZBlock m l -> ZBlock m l
prevEdge :: ZBlock m l -> ZBlock m l
firstEdge :: ZBlock m l -> ZBlock m l
lastEdge :: ZBlock m l -> ZBlock m l

nextEdge (ZBlock hd tl) = case tl of
    ZLast _ -> error "Attempted to move zipper past end of block"
    ZTail m t -> ZBlock (ZHead hd m) t

prevEdge (ZBlock hd tl) = case hd of
    ZFirst _ -> error "Attempted to move zipper before start of block"
    ZHead h m -> ZBlock h (ZTail m tl)

firstEdge zb@(ZBlock hd _) = case hd of
    ZFirst _ -> zb
    _ -> firstEdge $ prevEdge zb

lastEdge zb@(ZBlock _ tl) = case tl of
    ZLast _ -> zb
    _ -> firstEdge $ nextEdge zb

-- Graph conversion and creation
focus :: BlockId -> LGraph m l -> ZGraph m l
unfocus :: ZGraph m l -> LGraph m l
emptyGraph :: Graph m l

-- Need blockid for iniital block for these
emptyLGraph :: BlockId -> LGraph m l
emptyZGraph :: BlockId -> ZGraph m l

focus bid (LGraph eid blocks) = case lookupBlock bid blocks of
    Nothing -> error "Attempt to focus non-existent block"
    (Just block) -> ZGraph eid (unzipB block) (removeBlock bid blocks)

unfocus (ZGraph eid fb@(ZBlock h t) blocks) = case lookupBlock focusBid blocks of
    Just _ -> error "Focused block in blocks table during unfocus op"
    Nothing -> LGraph eid (insertBlock focusBid (zipB fb) blocks)
    where focusBid = getBlockId fb

emptyGraph = Graph (ZLast LastExit) emptyBlockLookup
emptyLGraph bid = LGraph bid (insertBlock bid (initBlock bid) emptyBlockLookup)
emptyZGraph bid = ZGraph bid (unzipB (initBlock bid)) emptyBlockLookup

lgraphToGraph :: LGraph m l -> Graph m l
lgraphToGraph (LGraph bid blocks) = case lookupBlock bid blocks of
    Nothing -> error "Lgraph entry points to non-existent block"
    Just (Block _ ztail) -> Graph ztail (removeBlock bid blocks)

graphToLGraph :: BlockId -> Graph m l -> LGraph m l
graphToLGraph bid (Graph ztail blocks) = case lookupBlock bid blocks of
    Nothing -> LGraph bid blocks'
    Just _ -> error "Block Id for LGraph entry already in use"
  where blocks' = insertBlock bid (Block bid ztail) blocks

-- ZGraph Movement
entry :: LGraph m l -> ZGraph m l -- Focus first edge in entry block
entry lgraph@(LGraph entryId _) = focus entryId lgraph

-- List blocks in order close to program flow -
-- Implementation taken from GHC
postorderDFS :: (HavingSuccessors l) => LGraph m l -> [Block m l]
postorderDFS g@(LGraph _ blockenv) =
    let ZGraph bid eblock _ = entry g in
     zipB eblock : postOrderDFSfromExcept blockenv eblock (singleBlockSet bid)

postOrderDFSfromExcept :: (HavingSuccessors b, HavingSuccessors l)
                          => BlockLookup m l -> b -> BlockSet -> [Block m l]

postOrderDFSfromExcept blocks b visited =
  vchildren (get_children b) (\acc _visited -> acc) [] visited
  where
    -- vnode ::
    --    Block m l -> ([Block m l] -> BlockSet -> a) -> [Block m l] -> BlockSet -> a
    vnode block@(Block bid _) cont acc visited =
        if elemBlockSet bid visited then
            cont acc visited
        else
            let cont' acc visited = cont (block:acc) visited in
            vchildren (get_children block) cont' acc (insertBlockSet bid visited)
    vchildren bs cont acc visited =
        let next children acc visited =
                case children of []     -> cont acc visited
                                 (b:bs) -> vnode b (next bs) acc visited
        in next bs acc visited
    get_children block = foldl add_id [] (succs block)
    add_id rst bid = case lookupBlock bid blocks of
                      Just b -> b : rst
                      Nothing -> rst

-- Graph querying

-- Get the predecessors of a block with certain blockid in the graph
predsOfBlock :: (LastNode l) => BlockLookup m l -> BlockId -> [Block m l]
predsOfBlock bLookup bid = filter (\b -> bid `elem` succs b) allBlocks
    where allBlocks = M.elems bLookup

-- Get the successors of a block with a certain blockid in the graph
succsOfBlock :: (LastNode l) => BlockLookup m l -> BlockId -> [Block m l]
succsOfBlock bLookup bid = case lookupBlock bid bLookup of
    Nothing -> error "Couldnt find block"
    Just b -> map (bLookup M.!) $ succs b

blockMiddles :: Block m l -> [m]
blockMiddles (Block _ (ZLast l)) = []
blockMiddles (Block bid (ZTail m zt)) = m : blockMiddles (Block bid zt)

--- Pretty printing of control flow graph structures.. 

instance (PrettyPrint m, PrettyPrint l, HavingSuccessors l) => PrettyPrint (ZTail m l) where
    ppr = pprZTail

instance (PrettyPrint l, HavingSuccessors l) => PrettyPrint (ZLast l) where
    ppr = pprLast

instance (PrettyPrint m, PrettyPrint l, HavingSuccessors l) => PrettyPrint (Graph m l) where
    ppr = pprGraph

instance (PrettyPrint m, PrettyPrint l, HavingSuccessors l) => PrettyPrint (LGraph m l) where
    ppr = pprLGraph

instance (PrettyPrint m, PrettyPrint l, HavingSuccessors l) => PrettyPrint (Block m l) where
    ppr = pprBlock

instance (PrettyPrint m, PrettyPrint l, HavingSuccessors l) => PrettyPrint (ZBlock m l) where
    ppr = pprBlock . zipB

instance PrettyPrint BlockId where
    ppr = text . getStr

pprZTail :: (PrettyPrint m, PrettyPrint l, HavingSuccessors l) => ZTail m l -> Doc
pprZTail (ZTail m t) = ppr m $$ ppr t
pprZTail (ZLast l) = ppr l

pprLast :: (PrettyPrint l, HavingSuccessors l) => ZLast l -> Doc
pprLast LastExit = text "leave\nret"
pprLast (LastOther l) = ppr l

pprBlock :: (PrettyPrint m, PrettyPrint l, HavingSuccessors l) => Block m l -> Doc
pprBlock (Block bid tl) = ppr bid <> colon
                                  $$ (nest 3 (ppr tl))

pprGraph (Graph ztail blocks) = vcat $ (ppr ztail) : map ppr (listBlocks blocks)
pprLGraph lgraph = vcat $ map ppr (postorderDFS lgraph)

-- Test data
testBlock :: Block Int SuccBlocks
testBlock = listToBlock (BID "Heyo") [1..10] Nothing
