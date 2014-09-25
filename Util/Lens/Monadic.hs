module Util.Lens.Monadic where

import Control.Applicative;
import Control.Arrow;
import Control.Category.Unicode;
import Control.Monad.Base;
import Control.Monad.Reader;
import Control.Monad.Writer;
import Control.Monad.Reader.Lens as ML;
import Control.Monad.Writer.Lens as ML;
import Control.Monad.ST;
import Data.STRef.Lifted;
import Data.Lens as L;

askModifySTRefM :: (MonadReader α m, MonadBase (ST s) m) => Lens α β (STRef s a) (STRef s a) -> (a -> m a) -> m ();
askModifySTRefM l φ = () <$ askReadModifySTRefM l φ;

askReadModifySTRefM :: (MonadReader α m, MonadBase (ST s) m) => Lens α β (STRef s a) (STRef s a) -> (a -> m a) -> m a;
askReadModifySTRefM l φ = ML.asks l >>= \ ref -> readSTRef ref >>= liftA2 (<$) id (φ >=> writeSTRef ref);

askModifySTRef :: (MonadReader α m, MonadBase (ST s) m) => Lens α β (STRef s a) (STRef s a) -> (a -> a) -> m ();
askModifySTRef l φ = askModifySTRefM l (return ∘ φ);

askReadModifySTRef :: (MonadReader α m, MonadBase (ST s) m) => Lens α β (STRef s a) (STRef s a) -> (a -> a) -> m a;
askReadModifySTRef l φ = askReadModifySTRefM l (return ∘ φ);

askReadWriteSTRefM :: (MonadReader α m, MonadBase (ST s) m) => Lens α β (STRef s a) (STRef s a) -> m a -> m a;
askReadWriteSTRefM l x = askReadModifySTRefM l (pure x);

askReadWriteSTRef :: (MonadReader α m, MonadBase (ST s) m) => Lens α β (STRef s a) (STRef s a) -> a -> m a;
askReadWriteSTRef l x = askReadModifySTRef l (pure x);

askWriteSTRefM :: (MonadReader α m, MonadBase (ST s) m) => Lens α β (STRef s a) (STRef s a) -> m a -> m ();
askWriteSTRefM l x = () <$ askReadWriteSTRefM l x;

askWriteSTRef :: (MonadReader α m, MonadBase (ST s) m) => Lens α β (STRef s a) (STRef s a) -> a -> m ();
askWriteSTRef l x = () <$ askReadWriteSTRef l x;
