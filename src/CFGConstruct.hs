module CFGConstruct where

import Control.Monad
import PrettyPrint
import Data.Char
import CFGConcrete
import MonadUniqueEnv

newtype AGraph m l = AGraph (Graph m l -> UniqStringEnv (Graph m l))

-- Compose AGraphs sequentially
(<&>) :: AGraph m l -> AGraph m l -> AGraph m l
AGraph f1 <&> AGraph f2 = AGraph (\x -> f2 x >>= f1)

foldAGraphs = foldr (<&>) emptyAGraph

-- Constructing AGraphs

emptyAGraph :: AGraph m l
emptyAGraph = AGraph return

mkLabel :: (LastNode l) => BlockId -> AGraph m l
mkLabel bid = AGraph f
    where f (Graph ztail blocks) = return $ 
            Graph (ZLast $ LastOther (mkBranchNode bid))
                  (insertBlock bid (Block bid ztail) blocks)

mkLabelFromStr :: (LastNode l) => String -> AGraph m l
mkLabelFromStr = mkLabel . BID

mkMiddle :: m -> AGraph m l
mkMiddle m = AGraph f
    where f (Graph zt blocks) = return $ 
            Graph (ZTail m zt) blocks

mkMiddles :: [m] -> AGraph m l
mkMiddles ms = foldAGraphs $ map mkMiddle ms

mkIfElse :: (PrettyPrint m, PrettyPrint l, LastNode l) => 
    (BlockId -> BlockId -> AGraph m l) -> AGraph m l -> AGraph m l -> AGraph m l
mkIfElse condBranch tBlk fBlk = 
    withNewBlockId ".endif" $ \endLbl ->
    withNewBlockId ".if_true" $ \trueLbl ->
    withNewBlockId ".if_false" $ \falseLbl ->
        condBranch trueLbl falseLbl <&>
        mkLabel trueLbl <&> tBlk <&> mkBranch endLbl <&>
        mkLabel falseLbl <&> fBlk <&> mkLabel endLbl

mkWhile :: (PrettyPrint m, PrettyPrint l, LastNode l) => 
    (BlockId -> BlockId -> AGraph m l) -> AGraph m l -> AGraph m l
mkWhile condBranch body = 
    withNewBlockId ".loop_test" $ \testId ->
    withNewBlockId ".loop_body" $ \bodyId ->
    withNewBlockId ".loop_end" $ \endId ->
        mkBranch testId <&> mkLabel bodyId <&>
        body <&> mkLabel testId <&> condBranch bodyId endId <&>
        mkLabel endId

mkFor :: (PrettyPrint m, PrettyPrint l, LastNode l) => 
    (BlockId -> BlockId -> AGraph m l) -> AGraph m l -> AGraph m l
mkFor condBranch body = 
    withNewBlockId ".for_test" $ \testId ->
    withNewBlockId ".for_body" $ \bodyId ->
    withNewBlockId ".for_end" $ \endId ->
        mkBranch testId <&> mkLabel bodyId <&>
        body <&> mkLabel testId <&> condBranch bodyId endId <&>
        mkLabel endId


-- Makes the CFG for a method declaration
mkMethod :: (PrettyPrint m, PrettyPrint l, LastNode l) =>
    String -> AGraph m l -> AGraph m l -> AGraph m l
mkMethod name methodDecl methodBody = outOfLine $ mkLabel (BID name) <&> methodDecl <&> methodBody

mkLast :: (PrettyPrint m, PrettyPrint l, LastNode l) => l -> AGraph m l
mkLast l = AGraph f
    where f (Graph _ blocks) = return $ Graph (ZLast (LastOther l)) blocks

mkBranch :: (PrettyPrint m, PrettyPrint l, LastNode l) => BlockId -> AGraph m l
mkBranch bid = mkLast $ mkBranchNode bid

newBlockId :: String -> UniqStringEnv BlockId
newBlockId s = getUniqString s >>= return . BID

withNewBlockId :: String -> (BlockId -> AGraph m l) -> AGraph m l
withNewBlockId s bidFunc = AGraph f
    where f graph = do
              bid <- newBlockId s
              let AGraph g = bidFunc bid
              g graph

outOfLine :: (LastNode l, PrettyPrint l, PrettyPrint m) => 
                AGraph m l -> AGraph m l

outOfLine (AGraph f) = AGraph f'
    where f' (Graph ztail' blocks') = do
                Graph ztail blocks <- f emptyGraph
                return $ Graph ztail' (mergeBlockLookups blocks blocks')

-- Converting AGraphs to concrete types
graphFromAGraph :: AGraph m l -> Graph m l
graphFromAGraph (AGraph f) = removeUniqEnv $ f emptyGraph

lgraphFromAGraph :: AGraph m l -> LGraph m l
lgraphFromAGraph g = removeUniqEnv $ do
    bid <- newBlockId "Graph starting point"
    labelAGraph bid g

lgraphFromAGraphBlocks :: BlockId -> AGraph m l -> LGraph m l
lgraphFromAGraphBlocks bid (AGraph f) = let Graph _ blocks = removeUniqEnv $ f emptyGraph in
                                            LGraph bid blocks

labelAGraph :: BlockId -> AGraph m l -> UniqStringEnv (LGraph m l)
labelAGraph bid (AGraph f) = do
    Graph ztail blocks <- f emptyGraph
    return $ LGraph bid $ insertBlock bid (Block bid ztail) blocks


-- Convenience
ztailFromMiddles :: (PrettyPrint m, PrettyPrint l, LastNode l) =>
    [m] -> ZLast l -> ZTail m l
ztailFromMiddles [] zl = ZLast zl
ztailFromMiddles (m:ms) zl = ZTail m (ztailFromMiddles ms zl)

ztailCollectMiddles :: (PrettyPrint m, PrettyPrint l, LastNode l) =>
    ZTail m l -> [m]
ztailCollectMiddles (ZLast _) = []
ztailCollectMiddles (ZTail m zt) = m : ztailCollectMiddles zt

mapZTailMiddles :: (PrettyPrint l, PrettyPrint m1, PrettyPrint m2, LastNode l) =>
    (m1 -> [m2]) -> ZTail m1 l -> ZTail m2 l
mapZTailMiddles f ztail = mapZTail f (\x -> (([],[]), x)) ztail

mapZTail:: (PrettyPrint l1, PrettyPrint l2, PrettyPrint m1, PrettyPrint m2, LastNode l1, LastNode l2) =>
    (m1 -> [m2]) -> (ZLast l1 -> (([m2],[m2]), ZLast l2)) -> ZTail m1 l1 -> ZTail m2 l2

mapZTail fm fl ztail = let zl = getZLast ztail
                           ((preMids, endMids), zl') = fl zl in
                              ztailFromMiddles (preMids ++ mappedMiddles ++ endMids) zl'
    where mappedMiddles = concatMap fm $ ztailCollectMiddles ztail

mapBlock:: (PrettyPrint l1, LastNode l1, PrettyPrint l2, LastNode l2, PrettyPrint m1, PrettyPrint m2) =>
    (BlockId -> m1 -> [m2]) -> (BlockId -> ZLast l1 -> (([m2],[m2]), ZLast l2)) -> Block m1 l1 -> Block m2 l2
mapBlock mf lf (Block bid ztail) = Block bid (mapZTail (mf bid) (lf bid) ztail)

mapLGraphNodes :: (PrettyPrint l1, LastNode l1, PrettyPrint l2, LastNode l2, PrettyPrint m1, PrettyPrint m2) => 
    (BlockId -> m1 -> [m2]) -> (BlockId -> ZLast l1 -> (([m2],[m2]), ZLast l2)) -> LGraph m1 l1 -> LGraph m2 l2

mapLGraphNodes mf lf (LGraph entryId blocks) = LGraph entryId blocks'
    where blocks' = mapBlocks (mapBlock mf lf) blocks

----------------------AUGMENTED WITH ZLAST TO DO BREAKS



mapWithZLastBlock:: (PrettyPrint l1, LastNode l1, PrettyPrint l2, LastNode l2, PrettyPrint m1, PrettyPrint m2) =>
    (ZLast l1 -> BlockId -> m1 -> [m2]) -> (BlockId -> ZLast l1 -> (([m2],[m2]), ZLast l2)) -> Block m1 l1 -> Block m2 l2
mapWithZLastBlock mf lf (Block bid ztail) = Block bid (mapZTail (mf (getZLast ztail) bid) (lf bid) ztail)

mapWithZLastLGraphNodes :: (PrettyPrint l1, LastNode l1, PrettyPrint l2, LastNode l2, PrettyPrint m1, PrettyPrint m2) => 
    (ZLast l1 -> BlockId -> m1 -> [m2]) -> (BlockId -> ZLast l1 -> (([m2],[m2]), ZLast l2)) -> LGraph m1 l1 -> LGraph m2 l2

mapWithZLastLGraphNodes mf lf (LGraph entryId blocks) = LGraph entryId blocks'
    where blocks' = mapBlocks (mapWithZLastBlock mf lf) blocks



-- Pretty Printing

instance (PrettyPrint m, PrettyPrint l, LastNode l) => PrettyPrint (AGraph m l) where
    ppr = ppr . lgraphFromAGraphBlocks (BID "main")
