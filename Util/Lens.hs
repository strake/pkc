module Util.Lens where

import Control.Applicative;
import Data.Lens;
import Util;

fst3 :: Lens (a, b, c) (o, b, c) a o;
snd3 :: Lens (a, b, c) (a, o, c) b o;
þrd3 :: Lens (a, b, c) (a, b, o) c o;
fst3 = lens (\ (x, y, z) -> x) (\ x (_, y, z) -> (x, y, z));
snd3 = lens (\ (x, y, z) -> y) (\ y (x, _, z) -> (x, y, z));
þrd3 = lens (\ (x, y, z) -> z) (\ z (x, y, _) -> (x, y, z));

doubleLens :: Lens α α a1 b1 -> Lens α α a2 b2 -> Lens α α (a1, a2) (b1, b2);
doubleLens l1 l2 = lens (liftA2 (,) (get l1) (get l2)) (\ (x, y) -> set l1 x & set l2 y);

tripleLens :: Lens α α a1 b1 -> Lens α α a2 b2 -> Lens α α a3 b3 -> Lens α α (a1, a2, a3) (b1, b2, b3);
tripleLens l1 l2 l3 = lens (liftA3 (,,) (get l1) (get l2) (get l3)) (\ (x, y, z) -> set l1 x & set l2 y & set l3 z);
