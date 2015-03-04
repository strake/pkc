{-# LANGUAGE TemplateHaskell #-}

module Data.CodeGenTypes where

import Control.Applicative;
import Data.Traversable;
import Data.Lens.TH;
import Data.Map;
import Data.Monoid;
import Data.STRef;
import Data.Syntax as S;
import Data.Tag;
import Data.Word;
import LLVM.General.AST as LLVM;

type Ptr = Operand;

data MxnProp = MxnProp {
  _mxnpWordBits, _mxnpTrampolineSize, _mxnpTrampolineAlign :: Int
};

{- XXX:
 - cgInsRef, cgBlkRef, cgThisBlockNameRef not needed at top level, without any function;
 - factorize out into own structure
 -}
data CgR s a b = CgR {
  _cgMxnProp :: MxnProp,
  _cgName    :: b -> [Char],
  _cgTypes   :: Map b (TagT (S.Type a) () b),
  _cgTerms   :: Map b Ptr,
  _cgInsRef  :: STRef s [Named Instruction],
  _cgBlkRef  :: STRef s [BasicBlock],
  _cgRetType :: TagT (S.Type a) () b,
  _cgTermTypes :: Map b (TagT (S.Type a) () b),
  _cgThisBlockNameRef :: STRef s Name,
  _cgCountRef :: STRef s Word
};

data CgW = CgW {
  _cgDefns   :: [Definition]
};

instance Monoid CgW where {
  mempty = CgW {
    _cgDefns   = []
  };
  w1 `mappend` w2 = CgW {
    _cgDefns   = _cgDefns   w1 ++ _cgDefns   w2
  };
};

concat <$> traverse (mkLens (dropWhile (== '_'))) [''MxnProp, ''CgR, ''CgW];
