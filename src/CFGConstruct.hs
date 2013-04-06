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
            Graph (ZLast $ LastOther (mkSingleBranchNode bid))
                  (insertBlock bid (Block bid ztail) blocks)

mkMiddle :: m -> AGraph m l
mkMiddle m = AGraph f
    where f (Graph zt blocks) = return $ 
            Graph (ZTail m zt) blocks

mkMiddles :: [m] -> AGraph m l
mkMiddles ms = foldAGraphs $ map mkMiddle ms

mkIfElse = undefined
mkWhile = undefined

mkLast :: (PrettyPrint m, PrettyPrint l, LastNode l) => l -> AGraph m l
mkLast = undefined

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

outOfLine = undefined

-- Converting AGraphs to concrete types
graphFromAGraph :: AGraph m l -> Graph m l
graphFromAGraph (AGraph f) = removeUniqEnv $ f emptyGraph

lgraphFromAGraph :: AGraph m l -> LGraph m l
lgraphFromAGraph = undefined

labelAGraph :: AGraph m l -> LGraph m l
labelAGraph (AGraph f) = undefined
