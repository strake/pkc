module Destruct (destruct) where

import Control.Applicative;
import Control.Arrow;
import Control.Category.Unicode;
import Data.Function (on);
import Data.Lens;
import qualified Data.List as List;
import Data.LTree;
import Data.Map (Map);
import qualified Data.Map as Map;
import Data.Syntax;
import Data.Traversable;
import Control.Monad.Reader;
import Control.Monad.Reader.Lens as ML;
import Util;

-- convert from structs with named members to tuples
-- involves tedious traversal of AST, alas
destruct :: ∀ α β b c m .
            (Ord b, Applicative m, MonadReader α m) => (∀ a . b -> m a) -> Lens α α (Map b (TagT Type γ b)) (Map b (TagT Type γ b)) -> Lens α β (Map b (TagT Type γ b)) c -> TagT Type γ b -> TagT Expr γ b -> m (TagT Expr γ b);
destruct fail =
  let {
    lu :: ∀ β c . (Applicative m, MonadReader α m, Ord b) => Lens α β (Map b (Type b)) c -> b -> m (Type b);
    lu l v = Map.lookup v <$> ML.asks l >>= maybe (fail v) return;
  } in \ lt lT ->
  let {
    luT (NamedType v) = lu lT v >>= luT;
    luT t = return t;

    select :: (Eq b) => Either (LTree [] Int) (LTree [] b) -> Type b -> Type b;
    select (Left  (Leaf k)) (TupleType ts) = ts !! (k-1);
    select (Left  (Stem ts)) t = TupleType (flip select t ∘ Left  <$> ts);
    select (Right (Leaf v)) (StructType ms) | Just t <- List.lookup (Just v) ms = t;
    select (Right (Stem ts)) t = TupleType (flip select t ∘ Right <$> ts);
    select (Left kt) (StructType ms) = select (Left kt) (TupleType (snd <$> ms));

    -- with rude partial type inference
    destruct' :: Maybe (Type b) -> Expr b -> m (Expr b, Type b);
    destruct' _ (Var v) = (,) (Var v) <$> (lu lt v >>= luT);
    destruct' m_t (Ptr x) = (Ptr *** PtrType) <$> destruct' ((\ (PtrType t) -> t) <$> m_t) x;
    destruct' m_t (Follow x) = destruct' (PtrType <$> m_t) x >>= return ∘ Follow *=* \ (PtrType t) -> luT t;
    destruct' m_t (Call f x) = destruct' Nothing f >>= \ (f, FuncType s t) -> flip (,) t ∘ Call f ∘ fst <$> destruct' (Just s) x;
    destruct' _ (Member x (Left  kt)) = destruct' Nothing x >>= return ∘ flip Member (Left kt) *=* (select (Left kt) >>> luT);
    destruct' _ (Member x (Right vt)) =
      destruct' Nothing x >>= \ (x, StructType ms) ->
      flip (,) (TupleType (snd <$> ms)) ∘ Member x ∘ Left <$>
      traverse (\ v -> maybe (fail v) (return ∘ (+1)) $ List.findIndex ((== Just v) ∘ fst) ms) vt;
    destruct' m_t (Tuple xs) =
      (unzip >>> Tuple *** TupleType) <$>
      case m_t of {
        Just (TupleType ts) -> zipWithA destruct' (Just <$> ts) xs;
        _ -> traverse (destruct' Nothing) xs;
      };
    destruct' (Just (StructType ms)) (Struct mm) | Just xs <- traverse (>>= flip Map.lookup mm) (fst <$> ms) = return (Tuple xs, TupleType (snd <$> ms));
    destruct' _ x@(Literal l) = let { t (LInteger n) = IntegralType True; t (LTuple ls) = TupleType (t <$> ls); } in return (x, t l);
    destruct' _ (PrimOp op xs) = (unzip >>> PrimOp op *** list (TupleType []) pure) <$> traverse (destruct' Nothing) xs;
    destruct' _ (Cast t x) =
      luT t >>= \ t ->
      case (t, x) of {
        -- cast to disambiguate struct type; recursive call must give wanted type
        (StructType ms, Struct mm) -> destruct' (Just t) x;

        -- true cast; recursive call gives whatever type, what we here cast
        _ -> flip (,) t ∘ Cast t ∘ fst <$> destruct' Nothing x;
      };
    destruct' m_t (If p x y) = (liftA3 (\ (p, _) (x, t) (y, _) -> (If p x y, t)) (destruct' Nothing p) `on` destruct' m_t) x y;
    destruct' m_t (Conj x y) = (liftA2 (\ (x, t) (y, _) -> (Conj x y, t)) `on` destruct' m_t) x y;
    destruct' m_t (Disj x y) = (liftA2 (\ (x, t) (y, _) -> (Disj x y, t)) `on` destruct' m_t) x y;
    destruct' _ (y := x) = destruct' Nothing y >>= \ (y, t) -> flip (,) (TupleType []) ∘ (y :=) ∘ fst <$> destruct' (Just t) x;
    destruct' m_t (With bm x) = (With bm *** id) <$> ML.local lt (Map.union bm) (destruct' m_t x);
    destruct' m_t (Then x y) = liftA2 (\ (x, _) (y, t) -> (Then x y, t)) (destruct' Nothing x) (destruct' m_t y);
    destruct' _ (Loop p x y) = flip (,) (TupleType []) <$> (liftA3 Loop `onn` fmap fst ∘ destruct' Nothing) p x y;
    destruct' _ (Return m_x) = return (Return m_x, TupleType []);
  } in fmap fst ∘∘ destruct' ∘ Just;
