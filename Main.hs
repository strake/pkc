module Main where

import Control.Applicative;
import Control.Category.Unicode;
import Control.Monad.Except;
import Control.Monad.ST;
import Control.Monad.State;
import Control.Monad.Reader;
import Control.Monad.Writer;
import Data.CodeGenTypes;
import Data.Syntax;
import Data.Lens as L;
import Data.Map as Map;
import Data.STRef.Lifted;
import Data.Text.Pos;
import System.IO;
import Text.PrettyPrint.Mainland;
import Util.LLVM.Pretty;
import Parse;
import Lex;
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
       [("Int", IntegralType True),
        ("Nat", IntegralType False),
        ("Word", TypeInteger (fromIntegral $ L.get mxnpWordBits mxnProp))],
     _cgName = id,
     _cgCountRef = countRef
   }) ∘ execWriterT ∘ genDecls ∘ either error id >>= print ∘ stack ∘ fmap ppr ∘ _cgDefns;

mxnProp = MxnProp {
  _mxnpWordBits = 64,
  _mxnpTrampolineSize = 72,
  _mxnpTrampolineAlign = 16
};
