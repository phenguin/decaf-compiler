{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module MonadUniqueEnv where

import Control.Monad
import Control.Monad.State
import Control.Applicative
import qualified Data.Map as M

newtype UniqEnv s a = UniqSE { getInternalSM :: State (M.Map s Integer) a }
type UniqStringEnv a = UniqEnv String a

instance Functor (UniqEnv s) where
    fmap f (UniqSE sf) = UniqSE $ fmap f sf

instance Monad (UniqEnv s) where
    return x = UniqSE $ return x
    (UniqSE sf) >>= f = UniqSE $ sf >>= (getInternalSM . f)

instance MonadState (M.Map s Integer) (UniqEnv s) where
    get = UniqSE $ get
    put x = UniqSE $ put x

instance Applicative (UniqEnv s) where
    pure x = UniqSE $ pure x
    (<*>) = ap

removeUniqEnv :: UniqEnv s a -> a
removeUniqEnv (UniqSE sf) = fst $ runState sf M.empty

getUniqString :: String -> UniqStringEnv String
getUniqString s = do
        stringMap <- get
        let i = M.findWithDefault 0 s stringMap
        modify (M.insert s (i+1))
        return (s ++ "_" ++ show i)


