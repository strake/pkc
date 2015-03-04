{-# LANGUAGE StandaloneDeriving #-}

module Main where

import Control.Applicative;
import Control.Category.Unicode;
import Control.Monad.Base;
import Control.Monad.Except;
import Control.Monad.ST;
import Control.Monad.State;
import Control.Monad.Reader;
import Control.Monad.Reader.Lens as ML;
import Control.Monad.Writer;
import Data.CodeGenTypes;
import Data.Syntax;
import Data.LTree;
import Data.Lens as L;
import Data.List as List;
import Data.Map as Map;
import Data.Maybe;
import Data.STRef.Lifted;
import Data.Tag;
import Data.Text.Pos;
import System.IO;
import Text.PrettyPrint.Mainland;
import Util.LLVM.Pretty;
import Parse;
import Lex;
import TypChk;
import CodeGen;

main =
  stToIO (newSTRef 0) >>= \ countRef ->
  getContents >>= runExceptT ∘ evalStateT Parse.top ∘ (\ xs -> LexSt { _lexInput = xs, _lexPos = TextPos (1,0) }) >>=
  stToIO ∘
  flip runReaderT
  (CgR {
     _cgMxnProp = mxnProp,
     _cgTerms = Map.empty,
     _cgTypes =
       Map.fromList
       [("Int", TagT () (IntegralType True)),
        ("Nat", TagT () (IntegralType False)),
        ("Word", TagT () (TypeInteger (fromIntegral $ L.get mxnpWordBits mxnProp)))],
     _cgTermTypes = Map.empty,
     _cgName = id,
     _cgCountRef = countRef
   }) ∘ execWriterT ∘
  (runExceptT ∘ typChkDecls cgTermTypes cgTypes cgRetType id id (lens (\ (x,_,_,y,z) -> (x,y,z)) (\ (x,y,z) (_,u,v,_,_) -> (x,u,v,y,z))) >=>
   genDecls id ∘ either (error ∘ show) id) ∘ either error id >>= print ∘ stack ∘ fmap ppr ∘ _cgDefns;

mxnProp = MxnProp {
  _mxnpWordBits = 64,
  _mxnpTrampolineSize = 72,
  _mxnpTrampolineAlign = 16
};

instance Show (TypChkFailure [Char] [Char]) where {
  show (UnboundFailure (either id id -> v)) = "Unbound name: " ++ v;
  show (MismatchFailure s t) = "Type mismatch: " ++ either id (show ∘ unTagT) s ++ " ≁ " ++ either id (show ∘ unTagT) t;
  show (AmbiguousFailure) = "Ambiguous type";
};

instance Show (Type [Char] tag [Char]) where {
  show (NamedType v) = show v;
  show (PtrType (TagT _ t)) = show t ++ " *";
  show (TupleType ts) = "(" ++ intercalate ", " (show ∘ unTagT <$> ts) ++ ")";
  show (FuncType (TagT _ s) (TagT _ t)) = show s ++ " -> " ++ show t;
  show (IntegralType True) = "Int";
  show (IntegralType False) = "Nat";
  show (TypeInteger n) = show n;
  show (StructType ms) = "{ " ++ List.intercalate ", " ((\ (m_v, TagT _ t) -> fromMaybe "_" m_v ++ " : " ++ show t) <$> ms) ++ " }";
  show (Typlication (TagT _ f) (TagT _ x)) = show f ++ " " ++ show x;
  show (TypeType) = "*";
};

deriving instance (Show a) => Show (LTree [] a);

instance Show Literal where {
  show (LInteger n) = show n;
  show (LTuple ls) = "(" ++ List.intercalate ", " (show <$> ls) ++ ")";
};
