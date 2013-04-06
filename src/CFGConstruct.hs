module CFGConstruct where

import Control.Monad
import PrettyPrint
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
    withNewBlockId "endif" $ \endLbl ->
    withNewBlockId "if_true" $ \trueLbl ->
    withNewBlockId "if_false" $ \falseLbl ->
        condBranch trueLbl falseLbl <&>
        mkLabel trueLbl <&> tBlk <&> mkBranch endLbl <&>
        mkLabel falseLbl <&> fBlk <&> mkLabel endLbl

mkWhile :: (PrettyPrint m, PrettyPrint l, LastNode l) => 
    (BlockId -> BlockId -> AGraph m l) -> AGraph m l -> AGraph m l
mkWhile condBranch body = 
    withNewBlockId "loop_test" $ \testId ->
    withNewBlockId "loop_body" $ \bodyId ->
    withNewBlockId "loop_end" $ \endId ->
        mkBranch testId <&> mkLabel bodyId <&>
        body <&> mkLabel testId <&> condBranch bodyId endId <&>
        mkLabel endId


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
                return Graph ztail' (mergeBlockLookups blocks blocks')

-- Converting AGraphs to concrete types
graphFromAGraph :: AGraph m l -> Graph m l
graphFromAGraph (AGraph f) = removeUniqEnv $ f emptyGraph

lgraphFromAGraph :: AGraph m l -> LGraph m l
lgraphFromAGraph g = removeUniqEnv $ do
    bid <- newBlockId "Graph starting point"
    labelAGraph bid g

labelAGraph :: BlockId -> AGraph m l -> UniqStringEnv (LGraph m l)
labelAGraph bid (AGraph f) = do
    Graph ztail blocks <- f emptyGraph
    return $ LGraph bid $ insertBlock bid (Block bid ztail) blocks

-- Pretty Printing

instance (PrettyPrint m, PrettyPrint l) => PrettyPrint (AGraph m l) where
    ppr = ppr . lgraphFromAGraph
