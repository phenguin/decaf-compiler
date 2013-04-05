module ControlFlow where

import qualified Data.Map as M

-- Implement control flow graph based off of GHCs own implementation
-- and the paper "An Applicative Control Flow Graph based on Huet's Zipper"

type BlockLookup m l = M.Map BlockId (Block m l)
type BlockId = Int

newtype SuccBlocks = SuccBlocks { getSuccBlocks :: [BlockId] } deriving (Show, Eq, Ord)

data ZLast l = LastExit | LastOther l deriving (Show)

data ZHead m = ZFirst BlockId
             | ZHead (ZHead m) m deriving (Show)

data ZTail m l = ZLast (ZLast l)
             | ZTail m (ZTail m l) deriving (Show)

data Block m l = Block { bId :: BlockId,
                         bTail :: ZTail m l } deriving (Show)

data ZBlock m l = ZBlock { zbHead :: ZHead m, 
                         zbTail :: ZTail m l } deriving (Show)

data Graph m l = Graph { gEntry :: ZTail m l,
                   gBlocks :: BlockLookup m l } deriving (Show)

data LGgraph m l = LGraph { lgEntry :: BlockId,
                            lgBlocks :: BlockLookup m l } deriving (Show)

data ZGraph m l = ZGraph { fgEntry :: BlockId,
                            fgFocus :: ZBlock m l, 
                            fgBlocks :: BlockLookup m l } deriving (Show)

class HavingZLast a where
    getZLast :: (a l) -> ZLast l

class HavingSuccessors l where
    succs :: l -> [BlockId]
    foldSuccs :: (BlockId -> a -> a) -> l -> a -> a
    foldSuccs add l z = foldr add z $ succs l

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





























