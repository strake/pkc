module TypChk (TypChkFailure (..), typChk, typChkDecls) where

import Prelude hiding (foldr);

import Control.Applicative;
import Control.Arrow;
import Control.Category.Unicode;
import Control.Monad;
import Control.Monad.Except;
import Control.Monad.Reader;
import Control.Monad.Reader.Lens as ML;
import Data.Eq.Unicode;
import Data.Foldable;
import Data.Foldable.Unicode;
import Data.Function (on);
import Data.Functor2;
import Data.LTree;
import Data.Lens;
import qualified Data.List as List;
import Data.Map (Map);
import qualified Data.Map as Map;
import Data.Maybe;
import Data.PrimOp;
import Data.Syntax;
import Data.Tag;
import Data.Traversable;
import Util;

import Debug.Trace;

data TypChkFailure a b = UnboundFailure (Either a b) | MismatchFailure (Either [Char] (TagT (Type a) () b)) (Either [Char] (TagT (Type a) () b)) | AmbiguousFailure;

typChkDecls :: (Ord b, Eq e, Traversable v, Applicative m, MonadReader ρ m, MonadError (α, TypChkFailure e b) m) =>
  Lens ρ ρ (Map b (TagT (Type e) () b)) (Map b (TagT (Type e) () b)) -> Lens ρ σ (Map b (TagT (Type e) () b)) c -> Lens ρ ρ (TagT (Type e) () b) (TagT (Type e) () b) ->
  Lens α β a (TagT (Type e) () b) -> Lens β β (TagT (Type e) () b) (TagT (Type e) () b) ->
  Lens x y (Decl e α b, TagT (Type e) α b, Maybe (TagT (Expr e) α b)) (Decl e β b, TagT (Type e) β b, Maybe (TagT (Expr e) β b)) -> v x -> m (v y);
typChkDecls lt lT lRet l' l'' l xs =
  ML.local lt (Map.union $ foldr (get l & \ (d, t, _) -> Map.insert (declName d) (declType (fmap2 (pure ()) d) (fmap2 (pure ()) t))) Map.empty xs) $
  traverse
  (l $ \ case {
     (d, t, Just x) ->
       ML.local lRet (pure (fmap2 (pure ()) t)) ∘
       ML.local lt
       (Map.union
        ((case d of {
          VarDecl _ -> id;
          FuncDecl _ parm -> flip (foldr (\ case { (Just v, t) -> Map.insert v (fmap2 (pure ()) t); _ -> id; })) parm;
        }) Map.empty)) $
       tripleA (fmap2 (set l' (TagT () TypeType))) (fmap2 (set l' (TagT () TypeType))) id ∘ (,,) d t ∘ Just <$> typChk lt lT lRet l' l'' (Just (fmap2 (pure ()) t)) x;
     (d, t, Nothing) -> return $ tripleA (fmap2 (set l' (TagT () TypeType))) (fmap2 (set l' (TagT () TypeType))) id (d, t, Nothing);
   }) xs;

typChk :: ∀ α β ρ σ τ a b c d e m . (Ord b, Eq e, Applicative m, MonadReader ρ m, MonadError (α, TypChkFailure e b) m) =>
  Lens ρ ρ (Map b (TagT (Type e) () b)) (Map b (TagT (Type e) () b)) -> Lens ρ σ (Map b (TagT (Type e) () b)) c -> Lens ρ τ (TagT (Type e) () b) d ->
  Lens α β a (TagT (Type e) () b) -> Lens β β (TagT (Type e) () b) (TagT (Type e) () b) ->
  Maybe (TagT (Type e) () b) -> TagT (Expr e) α b -> m (TagT (Expr e) β b);
typChk lt lT lRet l l' =
  let {
    typChk' :: Maybe (TagT (Type e) () b) -> TagT (Expr e) α b -> m (TagT (Expr e) β b);
    typChk' m_t (TagT n x) | Just (TagT () (NamedType v)) <- m_t = Just <$> (lu lT >=> can) v >>= flip typChk' (TagT n x)
                           | otherwise = case x of {
      Var v ->
        (lu lt >=> can) v >>= \ t ->
        case m_t of {
          Just s | t ≠ s -> throwError (n, (MismatchFailure `on` Right) s t);
          _ -> return (TagT (set l t n) (Var v));
        };
      Ptr x ->
        case m_t of {
          Nothing -> return Nothing;
          Just (TagT () (PtrType t)) -> return (Just t);
          Just s -> throwError (n, MismatchFailure (Right s) (Left "_*"));
        } >>= \ m_t ->
        (\ (TagT n x) -> TagT (modify l' (TagT () ∘ PtrType) n) (Ptr (TagT n x))) <$> typChk' m_t x;
      Follow x ->
        typChk' (TagT () ∘ PtrType <$> m_t) x >>= \ (TagT m x) ->
        case get l' m of {
          TagT _ (PtrType t) -> (\ t -> TagT (set l t n) (Follow (TagT m x))) <$> can t;
          s -> throwError (n, MismatchFailure (Left "_*") (Right s));
        };
      Call f x ->
        typChk' Nothing f >>= \ f ->
        case get l' (tag f) of {
          TagT () (FuncType s t) -> (\ x -> TagT (set l t n) (Call f x)) <$> typChk' (Just s) x;
          t -> throwError (n, MismatchFailure (Left "_ -> _") (Right t));
        };
      Member x sel -> typChk' Nothing x >>= (liftA2 ∘ liftA2) TagT (tag & l' (select sel & can)) (return ∘ flip Member sel);
      Tuple xs ->
        (\ xs -> TagT (set l (TagT () ∘ TupleType ∘ fmap (get l' ∘ tag) $ xs) n) (Tuple xs)) <$>
        case m_t of {
          Nothing                       -> zipWithA typChk' (repeat Nothing) xs;
          Just (TagT () (TupleType ts)) -> zipWithA typChk' (Just <$> ts)    xs;
          Just t -> throwError (n, MismatchFailure (Right t) (Left "(_, ..., _)"));
        };
      Struct mm ->
        maybe (throwError (n, AmbiguousFailure))
        (\ t@(TagT () (StructType ms)) ->
         TagT (set l t n) ∘ Struct <$>
         Map.traverseWithKey (\ v -> maybe (pure $ throwError (n, UnboundFailure (Left v))) (typChk' ∘ Just) (List.lookup (Just v) ms)) mm)
        m_t;
      Literal lit -> maybe (throwError (n, AmbiguousFailure)) (\ t -> TagT (set l t n) (Literal lit) <$ typChkLit' n m_t lit) m_t;
      PrimOp PrimNeg [x] -> (\ x@(TagT m _) -> TagT (set l (get l' m) n) (PrimOp PrimNeg [x])) <$> typChk' m_t x;
      PrimOp op [x,y]
        | op ∈ [PrimEq, PrimNEq, PrimGEq, PrimLEq, PrimGÞ, PrimLÞ] ->
          fmap (set (tagL ∘ l') boolTypeT) $
          failIfNonBoolT >> makeSameType2 n Nothing (mkPrim2 op) x y
        | op ∈ [PrimAnd, PrimOr, PrimXor] ->
          (liftA2 (,) `on` typChk' m_t) x y >>= uncurry (assertPrim2 n op)
        | op ∈ [PrimAdd] -> case m_t of {
            Just (TagT _ (PtrType _)) ->
              (liftA2 (,) `on` runError ∘ typChk' m_t) x y >>= \
              case {
                (Right x, Left (_, MismatchFailure _ _)) -> TagT (set l ((get l' ∘ tag) x) n) ∘ PrimOp PrimAdd ∘ (x:) ∘ pure <$> typChk' (Just (TagT () (IntegralType False))) y;
                (Left (_, MismatchFailure _ _), Right y) -> TagT (set l ((get l' ∘ tag) y) n) ∘ PrimOp PrimAdd ∘ (y:) ∘ pure <$> typChk' (Just (TagT () (IntegralType False))) x;
                (Right _, Right _) -> throwError (n, MismatchFailure (Left "pointer") (Left "integer"));
                (Left e, Left _) -> throwError e;
              };
            _ -> (liftA2 (,) `on` typChk' m_t) x y >>= uncurry (assertPrim2 n op);
          }
        | op ∈ [PrimShiftL, PrimRotL, PrimShiftR, PrimRotR] ->
          liftA2 (,) (typChk' m_t x) (typChk' Nothing y) >>= uncurry (cix2 (id pure) (id pure) op)
        | PrimMul <- op -> liftA2 (,) (typChk' Nothing x) (typChk' Nothing y) >>= uncurry (cix2 (||) (+) PrimMul)
        | PrimDiv <- op -> liftA2 (,) (typChk' m_t x) (typChk' Nothing y) >>= uncurry (cix2 (||) (id pure) PrimDiv)
        | PrimRem <- op -> liftA2 (,) (typChk' Nothing x) (typChk' m_t y) >>= uncurry (cix2 (\ _ _ -> False) (pure id) PrimRem)
        where {
          mkPrim2 op x y = PrimOp op [x,y];

          assertPrim2 n = assertOperands2 n ∘ mkPrim2;
  
          makeSameType2 n m_t@(Just _) f x y = (liftA2 (,) `on` typChk' m_t) x y >>= uncurry (assertOperands2 n f);
          makeSameType2 n Nothing f x y =
            (liftA2 (,) `on` runError ∘ typChk' Nothing) x y >>= \
            case {
              (Right x@(TagT (get l' -> s) _), Left (_, AmbiguousFailure)) -> TagT (set l s n) ∘ id   f x <$> typChk' (Just s) y;
              (Left (_, AmbiguousFailure), Right y@(TagT (get l' -> t) _)) -> TagT (set l t n) ∘ flip f y <$> typChk' (Just t) x;
              (Right x, Right y) -> assertOperands2 n f x y;
              (Left e, Left _) -> throwError e;
            };
  
          -- combine integral expressions
          cix2 :: (Bool -> Bool -> Bool) -> (Integer -> Integer -> Integer) -> PrimOp -> TagT (Expr e) β b -> TagT (Expr e) β b -> m (TagT (Expr e) β b);
          cix2 f g op x y = (\ t -> TagT (set l t n) (PrimOp op [x,y])) <$> (cit2 f g `on` get l' ∘ tag) x y;
  
          -- combine integral types
          cit2 :: (Bool -> Bool -> Bool) -> (Integer -> Integer -> Integer) -> TagT (Type e) () b -> TagT (Type e) () b -> m (TagT (Type e) () b);
          cit2 f g = liftA2 (\ (m, s) (n, t) -> integralTypeT (f s t) (g m n)) `on` integralWidthSign;
  
          integralWidthSign :: TagT (Type e) () b -> m (Integer, Bool);
          integralWidthSign (TagT _ (Typlication (TagT _ (IntegralType s)) (TagT _ (TypeInteger n)))) = return (n, s);
          integralWidthSign t = throwError (n, (MismatchFailure `on` Right) (TagT () (IntegralType True)) t); -- could also be unsigned
        };
      Cast t@(fmap2 (pure ()) -> s) x ->
        case (s, x) of {
          -- cast to disambiguate struct type; recursive call must give wanted type
          (TagT _ (StructType ms), TagT _ mm) -> typChk' (Just s) x;

          -- true cast; recursive call gives whatever type, what we here cast
          _ -> TagT (set l s n) ∘ Cast (fmap2 (set l (TagT () TypeType)) t) <$> typChk' Nothing x;
        };
      If p x y ->
        liftA3 (,,)
        (typChk' Nothing p)
        (typChk' m_t x) (typChk' m_t y) >>= \ (p, x, y) -> assertOperands2 n (If p) x y;
      Conj x y -> (liftA2 (,) `on` typChk' m_t) x y >>= uncurry (j Conj);
      Disj x y -> (liftA2 (,) `on` typChk' m_t) x y >>= uncurry (j Disj);
      y := x ->
        fmap (set (tagL ∘ l') unitTypeT) $
        failIfNonUnitT >> typChk' Nothing y >>= \ y@(TagT (get l' -> t) _) -> TagT (set l t n) ∘ (y :=) <$> typChk' (Just t) x;
      With bm x ->
        (\ x@(TagT m _) -> TagT (set l (get l' m) n) (With (fmap2 (set l (TagT () TypeType)) <$> bm) x)) <$>
        ML.local lt (Map.union (fmap2 (pure ()) <$> bm)) (typChk' m_t x);
      Then x y -> liftA2 (\ x y@(TagT m _) -> TagT (set l (get l' m) n) (Then x y)) (typChk' Nothing x) (typChk' m_t y);
      Loop p x y -> failIfNonUnitT >> liftA3 (TagT (set l unitTypeT n) ∘∘∘ Loop) (typChk' Nothing p) (typChk' Nothing x) (typChk' Nothing y);
      -- return expression has type (∀ a . a) for it ever has no value
      Return Nothing  -> return $ TagT (set l unitTypeT n) (Return Nothing);
      Return (Just x) -> ML.asks lRet >>= \ tRet -> TagT (set l (fromMaybe unitTypeT m_t) n) ∘ Return ∘ Just <$> typChk' (Just tRet) x;
    }
    where {
      -- canonicalize type
      can :: TagT (Type e) () b -> m (TagT (Type e) () b);
      can = unTagT & \ case {
        NamedType v -> (lu lT >=> can) v;
        PtrType t -> TagT () ∘ PtrType <$> can t;
        TupleType ts -> TagT () ∘ TupleType <$> traverse can ts;
        FuncType s t -> TagT () <$> (liftA2 FuncType `on` can) s t;
        IntegralType s -> return (TagT () (IntegralType s));
        TypeInteger n -> return (TagT () (TypeInteger n));
        StructType ms -> TagT () ∘ StructType <$> traverse (return *=* can) ms;
         UnionType ms ->  TagT () ∘ UnionType <$> traverse (return *=* can) ms;
        Typlication s t -> TagT () <$> (liftA2 Typlication `on` can) s t;
        TypeType -> return (TagT () TypeType);
      };

      lu :: ∀ σ c . Lens ρ σ (Map b (TagT (Type e) () b)) c -> b -> m (TagT (Type e) () b);
      lu l v = Map.lookup v <$> ML.asks l >>= maybe (throwError (n, UnboundFailure (Right v))) return;

      failIfNonBoolT = case m_t of {
        Nothing -> return ();
        Just (TagT _ (Typlication (TagT _ (IntegralType False)) (TagT _ (TypeInteger 1)))) -> return ();
        Just t -> throwError (n, (MismatchFailure `on` Right) t (TagT () (Typlication (TagT () (IntegralType False)) (TagT () (TypeInteger 1)))));
      };

      failIfNonUnitT = case m_t of {
        Nothing -> return ();
        Just (TagT _ (TupleType [])) -> return ();
        Just t -> throwError (n, (MismatchFailure `on` Right) t (TagT () (TupleType [])));
      };

      j f x y = case m_t of {
        Just (TagT _ (TupleType [])) -> return $ TagT (set l unitTypeT n) (f x y);
        Nothing -> return $ TagT (set l unitTypeT n) (f x y);
        _ -> assertOperands2 n f x y
      };

      typChkLit' :: α -> Maybe (TagT (Type e) () b) -> Literal -> m ();
      typChkLit' n m_t lit@(LInteger m) =
        case m_t of {
          Nothing -> throwError (n, AmbiguousFailure);
          Just (TagT () (Typlication (TagT () (IntegralType _)) (TagT () (TypeInteger _)))) -> return ();
          Just (TagT () (IntegralType _)) -> return ();
          Just t
            | (TagT () (PtrType _), 0) <- (t, m) -> return ()
            | True -> throwError (n, (MismatchFailure `on` Right) t (TagT () (IntegralType True)))
            ;
        };
      typChkLit' n m_t lit@(LTuple lits) =
        case m_t of {
          Nothing                       -> fold <$> zipWithA (typChkLit' n) (repeat Nothing) lits;
          Just (TagT () (TupleType ts)) -> fold <$> zipWithA (typChkLit' n) (Just <$> ts)    lits;
          Just t -> throwError (n, MismatchFailure (Right t) (Left "(_, ..., _)"));
        };

      -- assert operands have same type
      assertOperands2 n f x@(TagT (get l' -> s) _) y@(TagT (get l' -> t) _) = s ≠ t ? throwError (n, trace "assertOperands2" $ (MismatchFailure `on` Right) s t) $ return $ TagT (set l s n) (f x y);
    };
  } in typChk';

select :: (Eq a) => Either (LTree [] Int) (LTree [] a) -> TagT (Type a) () b -> TagT (Type a) () b;
select (Left  (Leaf k)) (TagT () (TupleType ts)) = ts !! (k-1);
select (Left  (Stem ts)) t = TagT () (TupleType (flip select t ∘ Left <$> ts));
select (Right (Leaf v)) (TagT () (StructType ms)) | Just t <- List.lookup (Just v) ms = t;
select (Right (Stem ts)) t = TagT () (TupleType (flip select t ∘ Right <$> ts));

boolTypeT :: TagT (Type a) () b;
boolTypeT = TagT () (Typlication (TagT () (IntegralType False)) (TagT () (TypeInteger 1)));

unitTypeT :: TagT (Type a) () b;
unitTypeT = TagT () (TupleType []);

integralTypeT :: Bool -> Integer -> TagT (Type a) () b;
integralTypeT s n = TagT () (Typlication (TagT () (IntegralType s)) (TagT () (TypeInteger n)));

f ∘∘∘ g = (f ∘) ∘∘ g;

runError :: (Functor m, MonadError e m) => m a -> m (Either e a);
runError m_x = catchError (Right <$> m_x) (return ∘ Left);
