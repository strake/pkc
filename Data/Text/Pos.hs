module Data.Text.Pos where

import Data.Monoid;

newtype TextPos = TextPos (Int, Int)
  deriving (Eq, Ord);

instance Show TextPos where {
  show (TextPos (m, n)) = show m ++ ":" ++ show n;
};

instance Num TextPos where {
  fromInteger n = TextPos (0, fromInteger n);
  TextPos (m, n) + TextPos (μ, ν) = TextPos (m+μ, n+ν);
};

infix 5 :–:;

data ConvexTextRange = TextPos :–: TextPos
                     | EmptyConvexTextRange
  deriving (Eq);

instance Show ConvexTextRange where {
  show (s :–: t) = show s ++ " – " ++ show t;
};

instance Monoid ConvexTextRange where {
  mempty = EmptyConvexTextRange;
  EmptyConvexTextRange `mappend` y = y;
  x `mappend` EmptyConvexTextRange = x;
  (s :–: t) `mappend` (σ :–: τ) = min s σ :–: max t τ;
};
