module Data.Tag where

import Control.Applicative;
import Control.Category.Unicode;
import Control.Monad;
import Data.Functor2;
import Data.Lens;
import Data.Monoid;
import Util;

data TagT t tag a = TagT tag (t tag a) deriving (Eq, Show);

instance (Functor (t tag)) => Functor (TagT t tag) where {
  f `fmap` TagT tag x = TagT tag (f <$> x);
};

instance (Functor2 t) => Functor2 (TagT t) where {
  f `fmap2` TagT tag x = TagT (f tag) (f `fmap2` x);
};

instance (Applicative (t tag), Monoid tag) => Applicative (TagT t tag) where {
  pure = TagT mempty ∘ pure;
  TagT s x <*> TagT t y = TagT (s <> t) (x <*> y);
};

unTagT :: TagT t tag a -> t tag a;
unTagT (TagT _ x) = x;

tag :: TagT t tag a -> tag;
tag (TagT t _) = t;

unTagL :: Lens (TagT s tag a) (TagT t tag b) (s tag a) (t tag b);
unTagL = lens unTagT (\ x (TagT t _) -> TagT t x);

tagL :: Lens (TagT t tag a) (TagT t tag a) tag tag;
tagL = lens tag (\ t (TagT _ x) -> TagT t x);
