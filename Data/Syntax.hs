module Data.Syntax where

import Control.Applicative;
import Control.Arrow;
import Control.Category.Unicode;
import Control.Monad;
import Data.Function (on);
import Data.Functor2;
import Data.LTree;
import Data.Lens;
import Data.Map (Map);
import qualified Data.Map as Map;
import Data.PrimOp;
import Data.Tag;
import Util;

data Decl a tag b
  = VarDecl b
  | FuncDecl b (LTree [] (Maybe b, TagT (Type a) tag b))
  ;

data Expr a tag b
  = Var b
  | Ptr (TagT (Expr a) tag b)
  | Follow (TagT (Expr a) tag b)
  | Call (TagT (Expr a) tag b) (TagT (Expr a) tag b)
  | Member (TagT (Expr a) tag b) (Either (LTree [] Int) (LTree [] a))
  | Tuple [TagT (Expr a) tag b]
  | Struct (Map a (TagT (Expr a) tag b))
  | Union (a, TagT (Expr a) tag b)
  | Literal Literal
  | PrimOp PrimOp [TagT (Expr a) tag b]
  | Cast (TagT (Type a) tag b) (TagT (Expr a) tag b)
  | If (TagT (Expr a) tag b) (TagT (Expr a) tag b) (TagT (Expr a) tag b)
  | Conj (TagT (Expr a) tag b) (TagT (Expr a) tag b)
  | Disj (TagT (Expr a) tag b) (TagT (Expr a) tag b)
  | TagT (Expr a) tag b := TagT (Expr a) tag b
  | With (Map b (TagT (Type a) tag b)) (TagT (Expr a) tag b)
  | Then (TagT (Expr a) tag b) (TagT (Expr a) tag b)
  | Loop (TagT (Expr a) tag b) (TagT (Expr a) tag b) (TagT (Expr a) tag b) -- Loop p x y in C = for (; p; x) y;
  | Return (Maybe (TagT (Expr a) tag b))
  ;

data Literal
  = LInteger Integer
  | LTuple [Literal]
  ;

data Type a tag b
  = NamedType b
  | PtrType (TagT (Type a) tag b)
  | TupleType [TagT (Type a) tag b]
  | FuncType (TagT (Type a) tag b) (TagT (Type a) tag b)
  | IntegralType Signedness -- :: Natural → *
  | TypeInteger Integer
  | StructType [(Maybe a, TagT (Type a) tag b)]
  |  UnionType [(Maybe a, TagT (Type a) tag b)]
  | Typlication (TagT (Type a) tag b) (TagT (Type a) tag b)
  | TypeType
  deriving (Eq, Functor);

type Mutability = Bool;
type Signedness = Bool;
type Width = Int;

declName :: Decl a tag b -> b;
declName (VarDecl v) = v;
declName (FuncDecl v _) = v;

declType :: Decl a () b -> TagT (Type a) () b -> TagT (Type a) () b;
declType (VarDecl _) = id;
declType (FuncDecl _ s) = TagT () ∘ FuncType (parmType s);

parmType :: LTree [] (c, TagT (Type a) () b) -> TagT (Type a) () b;
parmType (Leaf (_, t)) = t;
parmType (Stem parms)  = TagT () (TupleType (parmType <$> parms));

parmExpr :: LTree [] (Maybe b, TagT (Type a) () b) -> TagT (Expr a) (TagT (Type a) () b) (Maybe b);
parmExpr (Leaf (m_v, t)) = TagT t (Var m_v);
parmExpr (Stem parms)    = liftA2 TagT (TagT () ∘ TupleType ∘ fmap tag) Tuple (parmExpr <$> parms);

instance Functor (Expr a tag);

instance Functor2 (Decl a) where {
  fmap2 f (VarDecl v) = VarDecl v;
  fmap2 f (FuncDecl v argu) = FuncDecl v ((id *** fmap2 f) <$> argu);
};

instance Functor2 (Expr a) where {
  fmap2 f (Var v) = Var v;
  fmap2 f (Ptr x) = Ptr (fmap2 f x);
  fmap2 f (Follow x) = Follow (fmap2 f x);
  fmap2 f (Call x y) = (Call `on` fmap2 f) x y;
  fmap2 f (Member x sel) = Member (fmap2 f x) sel;
  fmap2 f (Tuple xs) = Tuple (fmap2 f <$> xs);
  fmap2 f (Struct ms) = Struct (fmap2 f <$> ms);
  fmap2 f (Union (v, x)) = Union (v, fmap2 f x);
  fmap2 f (Literal l) = Literal l;
  fmap2 f (PrimOp op xs) = PrimOp op (fmap2 f <$> xs);
  fmap2 f (Cast t x) = Cast (fmap2 f t) (fmap2 f x);
  fmap2 f (If p x y) = (If `onn` fmap2 f) p x y;
  fmap2 f (Conj x y) = (Conj `on` fmap2 f) x y;
  fmap2 f (Disj x y) = (Disj `on` fmap2 f) x y;
  fmap2 f (y := x) = ((:=) `on` fmap2 f) y x;
  fmap2 f (With bs x) = With (fmap2 f <$> bs) (fmap2 f x);
  fmap2 f (Then x y) = (Then `on` fmap2 f) x y;
  fmap2 f (Loop p x y) = (Loop `onn` fmap2 f) p x y;
  fmap2 f (Return m_x) = Return (fmap2 f <$> m_x);
};

instance Functor2 (Type a) where {
  fmap2 f (NamedType v) = NamedType v;
  fmap2 f (PtrType t) = PtrType (fmap2 f t);
  fmap2 f (TupleType ts) = TupleType (fmap2 f <$> ts);
  fmap2 f (FuncType s t) = (FuncType `on` fmap2 f) s t;
  fmap2 f (IntegralType s) = IntegralType s;
  fmap2 f (TypeInteger n) = TypeInteger n;
  fmap2 f (StructType ms) = StructType ((id *** fmap2 f) <$> ms);
  fmap2 f ( UnionType ms) =  UnionType ((id *** fmap2 f) <$> ms);
  fmap2 f (Typlication s t) = (Typlication `on` fmap2 f) s t;
  fmap2 f (TypeType) = TypeType;
};
