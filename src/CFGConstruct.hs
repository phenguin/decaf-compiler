module CFGConstruct where

import Control.Monad
import CFGConcrete
import MonadUniqueEnv

newtype AGraph m l = AGraph (Graph m l -> UniqStringEnv (Graph m l))

-- Compose AGraphs sequentially
(<&>) :: AGraph m l -> AGraph m l -> AGraph m l
AGraph f1 <&> AGraph f2 = AGraph (\x -> f2 x >>= f1)
