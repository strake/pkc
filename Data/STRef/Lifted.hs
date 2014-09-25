module Data.STRef.Lifted (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef) where

import Control.Category.Unicode;
import Control.Monad.Base;
import Control.Monad.ST;
import Data.STRef (STRef);
import qualified Data.STRef;
import Util;

newSTRef :: MonadBase (ST s) m => a -> m (STRef s a);
newSTRef = liftBase ∘ Data.STRef.newSTRef;

readSTRef :: MonadBase (ST s) m => STRef s a -> m a;
readSTRef = liftBase ∘ Data.STRef.readSTRef;

writeSTRef :: MonadBase (ST s) m => STRef s a -> a -> m ();
writeSTRef = liftBase ∘∘ Data.STRef.writeSTRef;

modifySTRef :: MonadBase (ST s) m => STRef s a -> (a -> a) -> m ();
modifySTRef = liftBase ∘∘ Data.STRef.modifySTRef;
