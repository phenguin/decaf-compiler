module CFGConcrete where

import qualified Data.Map as M
import PrettyPrint
import Text.PrettyPrint.HughesPJ

-- Implement control flow graph based off of GHCs own implementation
-- and the paper "An Applicative Control Flow Graph based on Huet's Zipper"

type BlockLookup m l = M.Map BlockId (Block m l)
type BlockId = Int

newtype SuccBlocks = SuccBlocks { getSuccBlocks :: [BlockId] } deriving (Show, Eq, Ord)

instance PrettyPrint SuccBlocks where
    ppr (SuccBlocks bs) = vcat $ map ppr bs

data ZLast l = LastExit | LastOther l deriving (Show, Eq)

data ZHead m = ZFirst BlockId
             | ZHead (ZHead m) m deriving (Show, Eq)

data ZTail m l = ZLast (ZLast l)
             | ZTail m (ZTail m l) deriving (Show, Eq)

data Block m l = Block { bId :: BlockId,
                         bTail :: ZTail m l } deriving (Show, Eq)

data ZBlock m l = ZBlock { zbHead :: ZHead m, 
                         zbTail :: ZTail m l } deriving (Show, Eq)

data Graph m l = Graph { gEntry :: ZTail m l,
                   gBlocks :: BlockLookup m l } deriving (Show, Eq)

data LGraph m l = LGraph { lgEntry :: BlockId,
                            lgBlocks :: BlockLookup m l } deriving (Show, Eq)

data ZGraph m l = ZGraph { fgEntry :: BlockId,
                            fgFocus :: ZBlock m l, 
                            fgBlocks :: BlockLookup m l } deriving (Show, Eq)

class HavingZLast a where
    getZLast :: (a l) -> ZLast l

class HavingBlockId a where
    getBlockId :: a -> BlockId

class HavingSuccessors l where
    succs :: l -> [BlockId]
    foldSuccs :: (BlockId -> a -> a) -> l -> a -> a
    foldSuccs add l z = foldr add z $ succs l

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

instance HavingSuccessors SuccBlocks where
    succs = getSuccBlocks

-- Utility functions

listToZTail :: (HavingSuccessors l) => [m] -> Maybe l -> ZTail m l
listToZTail [] Nothing = ZLast LastExit
listToZTail [] (Just l) = ZLast (LastOther l)
listToZTail (m:ms) ml = ZTail m (listToZTail ms ml)

listToBlock ms ml = (\zt -> Block 0 zt) $ listToZTail ms ml

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

focus bid (LGraph eid blocks) = case M.lookup bid blocks of
    Nothing -> error "Attempt to focus non-existent block"
    (Just block) -> ZGraph eid (unzipB block) (M.delete bid blocks)

unfocus (ZGraph eid fb@(ZBlock h t) blocks) = case M.lookup focusBid blocks of
    Just _ -> error "Focused block in blocks table during unfocus op"
    Nothing -> LGraph eid (M.insert focusBid (zipB fb) blocks)
    where focusBid = getBlockId fb

emptyGraph = Graph (ZLast LastExit) M.empty
emptyLGraph bid = LGraph bid (M.insert bid (initBlock bid) M.empty)
emptyZGraph bid = ZGraph bid (unzipB (initBlock bid)) M.empty

-- ZGraph Movement
entry :: LGraph m l -> ZGraph m l -- Focus first edge in entry block
entry = undefined

--- Pretty printing of control flow graph structures.. largely stolen from GHC

instance (PrettyPrint m, PrettyPrint l) => PrettyPrint (ZTail m l) where
    ppr = pprZTail

instance (PrettyPrint l) => PrettyPrint (ZLast l) where
    ppr = pprLast

instance (PrettyPrint m, PrettyPrint l) => PrettyPrint (Graph m l) where
    ppr = pprGraph

instance (PrettyPrint m, PrettyPrint l) => PrettyPrint (LGraph m l) where
    ppr = pprLGraph

instance (PrettyPrint m, PrettyPrint l) => PrettyPrint (Block m l) where
    ppr = pprBlock

instance (PrettyPrint m, PrettyPrint l) => PrettyPrint (ZBlock m l) where
    ppr = pprBlock . zipB

pprZTail :: (PrettyPrint m, PrettyPrint l) => ZTail m l -> Doc
pprZTail (ZTail m t) = ppr m $$ ppr t
pprZTail (ZLast l) = ppr l

pprLast :: (PrettyPrint l) => ZLast l -> Doc
pprLast LastExit = text "<exit>"
pprLast (LastOther l) = ppr l

pprBlock :: (PrettyPrint m, PrettyPrint l) => Block m l -> Doc
pprBlock (Block bid tl) = text "Block" <> ppr bid <> colon
                                       $$ (nest 3 (ppr tl))

pprGraph = undefined
pprLGraph = undefined

-- Test data
testBlock :: Block Int SuccBlocks
testBlock = listToBlock [1..10] Nothing
