module Main where

import Control.Applicative;
import Control.Category.Unicode;
import Control.Monad.ST;
import Control.Monad.Reader;
import Control.Monad.Writer;
import Data.CodeGenTypes;
import Data.Syntax;
import Data.Lens as L;
import Data.Map as Map;
import Data.STRef.Lifted;
import System.IO;
import Text.PrettyPrint.Mainland;
import Util.LLVM.Pretty;
import Parse;
import Lex;
import CodeGen;

main =
  stToIO (newSTRef 0) >>= \ countRef ->
  scan <$> getContents >>= Parse.top >>=
  stToIO ∘
  flip runReaderT
  (CgR {
     _cgMxnProp = mxnProp,
     _cgTerms = Map.empty,
     _cgTypes =
       Map.fromList
       [("Int", IntegralType True (L.get mxnpWordBits mxnProp)),
        ("Int8", IntegralType True 8),
        ("Int16", IntegralType True 16),
        ("Int32", IntegralType True 32),
        ("Int64", IntegralType True 64),
        ("Nat", IntegralType False (L.get mxnpWordBits mxnProp)),
        ("Nat8", IntegralType False 8),
        ("Nat16", IntegralType False 16),
        ("Nat32", IntegralType False 32),
        ("Nat64", IntegralType False 64)],
     _cgName = id,
     _cgCountRef = countRef
   }) ∘ execWriterT ∘ genDecls >>= print ∘ stack ∘ fmap ppr ∘ _cgDefns;

mxnProp = MxnProp {
  _mxnpWordBits = 64,
  _mxnpTrampolineSize = 72,
  _mxnpTrampolineAlign = 16
};
