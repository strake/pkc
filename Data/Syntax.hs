module Data.Syntax where

import Control.Applicative;
import Data.LTree;
import Data.Map (Map);
import qualified Data.Map as Map;
import Data.PrimOp;

data Decl b
  = VarDecl b
  | FuncDecl b (LTree [] (Maybe b, Type b))
  ;

data Expr b
  = Var b
  | Ptr (Expr b)
  | Follow (Expr b)
  | Call (Expr b) (Expr b)
  | Member (Expr b) (Either Int b)
  | Tuple [Expr b]
  | Struct (Map b (Expr b))
  | Union (b, Expr b)
  | Literal Literal
  | PrimOp PrimOp [Expr b]
  | Cast (Type b) (Expr b)
  | If (Expr b) (Expr b) (Expr b)
  | Conj (Expr b) (Expr b)
  | Disj (Expr b) (Expr b)
  | Expr b := Expr b
  | With (Map b (Type b)) (Expr b)
  | Then (Expr b) (Expr b)
  | Loop (Expr b) (Expr b) (Expr b) -- Loop p x y in C = for (; p; x) y;
  | Return (Maybe (Expr b))
  ;

data Literal
  = LInteger Integer
  | LTuple [Literal]
  ;

data Type b
  = NamedType b
  | PtrType (Type b)
  | TupleType [Type b]
  | FuncType (Type b) (Type b)
  | IntegralType Signedness -- :: Natural → *
  | TypeInteger Integer
  | StructType [(Maybe b, Type b)]
  |  UnionType [(Maybe b, Type b)]
  | Typlication (Type b) (Type b)
  | TypeType
  ;

type Mutability = Bool;
type Signedness = Bool;
type Width = Int;

declName :: Decl b -> b;
declName (VarDecl v) = v;
declName (FuncDecl v _) = v;

parmType :: LTree [] (a, Type b) -> Type b;
parmType (Leaf (_, t)) = t;
parmType (Stem parms)  = TupleType (parmType <$> parms);

parmExpr :: LTree [] (Maybe b, a) -> Expr b;
parmExpr (Leaf (Just v, _))  = Var v;
parmExpr (Leaf (Nothing, _)) = error "\"_\" in parm";
parmExpr (Stem parms)        = Tuple (parmExpr <$> parms);
