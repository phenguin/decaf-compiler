module UniqueStringEnv where

import Control.Monad
import Control.Monad.State
import Control.Applicative
import qualified Data.Map as M

newtype UniqEnv a = UniqSE { getInternalSM :: State (M.Map String Integer) a }

instance Functor UniqEnv where
    fmap f (UniqSE sf) = UniqSE $ fmap f sf

instance Monad UniqEnv where
    return x = UniqSE $ return x
    (UniqSE sf) >>= f = UniqSE $ sf >>= (getInternalSM . f)

instance Applicative UniqEnv where
    pure x = UniqSE $ pure x
    (<*>) = ap
