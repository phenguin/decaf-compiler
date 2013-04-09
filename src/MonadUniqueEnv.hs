{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module MonadUniqueEnv where

import Control.Monad
import Control.Monad.State
import Control.Applicative
import PrettyPrint
import qualified Data.Map as M

newtype UniqEnv s a = UniqSE { getInternalSM :: State (M.Map s Integer) a }
type UniqStringEnv a = UniqEnv String a
--
-- Kind of ghetto but okay for now
type UniqCounter a = UniqEnv Int a

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

instance (PrettyPrint a) => PrettyPrint (UniqEnv s a) where
    ppr x = ppr $ removeUniqEnv x

removeUniqEnv :: UniqEnv s a -> a
removeUniqEnv (UniqSE sf) = fst $ runState sf M.empty

getUniq :: (Ord a) => a -> UniqEnv a Integer
getUniq x = do
    uMap <- get
    let i = M.findWithDefault 0 x uMap
    modify (M.insert x (i+1))
    return i

freshIndex :: UniqCounter Integer
freshIndex = getUniq 0

-- Just check value of counter.. without incrementing it
checkCounter :: UniqCounter Integer
checkCounter = do
    uMap <- get
    let i = M.findWithDefault 0 0 uMap
    return i

getUniqString :: String -> UniqStringEnv String
getUniqString s = do
        i <- getUniq s
        return (s ++ "_" ++ show i)


