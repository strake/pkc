module CodeGen.Common where

import Prelude hiding (foldr, any);

import Control.Applicative;
import Control.Arrow;
import Control.Category.Unicode;
import Control.Monad.Base;
import Control.Monad.ST;
import Control.Monad.Reader as M;
import Control.Monad.State  as M;
import Control.Monad.Writer as M;
import Control.Monad.Reader.Lens as ML;
import Control.Monad.State.Lens  as ML;
import Control.Monad.Writer.Lens as ML;
import Data.CodeGenTypes;
import Data.PrimOp;
import Data.Eq.Unicode;
import Data.Ord.Unicode;
import Data.Foldable;
import Data.Foldable.Unicode;
import Data.Traversable;
import Data.Function (on);
import Data.Lens as L;
import qualified Data.List as List;
import Data.LTree;
import Data.Map (Map);
import qualified Data.Map as Map;
import Data.Set (Set);
import qualified Data.Set as Set;
import Data.Maybe;
import Data.Word;
import Data.STRef.Lifted;
import LLVM.General.AST as LLVM;
import LLVM.General.AST.AddrSpace as LLVM;
import LLVM.General.AST.Attribute as LLVM;
import LLVM.General.AST.Constant as LLVMC;
import LLVM.General.AST.CallingConvention as LLVM;
import LLVM.General.AST.Global as LLVM;
import LLVM.General.AST.InlineAssembly as LLVMAsm;
import LLVM.General.AST.IntegerPredicate as LLVMIP;
import LLVM.General.AST.Linkage as LLVML;
import LLVM.General.AST.Visibility as LLVMV;
import Util;
import Util.Lens.Monadic as ML;
import Util.LLVM.Type;

type MonadCodeGen s b m = (Ord b, Applicative m, MonadReader (CgR s b) m, MonadWriter (CgW) m, MonadBase (ST s) m);




genIf :: (MonadCodeGen s b m) => m Operand -> m Operand -> m Operand -> m Operand;
genIf m_p m_x m_y =
  fromIntegral <$> ML.asks (cgMxnProp ∘ mxnpWordBits) >>= \ w ->
  m_p >>= genCond >>= \ p ->
  liftA3 (,,) fresh fresh fresh >>= \ (xBlkName, yBlkName, outName) ->
  terminate (LLVM.CondBr p yBlkName xBlkName []) >>
  ML.askWriteSTRef cgThisBlockNameRef xBlkName >> m_x <* terminate (LLVM.Br outName []) >>= \ x ->
  ML.asks cgThisBlockNameRef >>= readSTRef >>= \ xBlkName ->
  ML.askWriteSTRef cgThisBlockNameRef yBlkName >> m_y <* terminate (LLVM.Br outName []) >>= \ y ->
  ML.asks cgThisBlockNameRef >>= readSTRef >>= \ yBlkName ->
  ML.askWriteSTRef cgThisBlockNameRef outName >>
  case operandType x of {
    LLVM.VoidType -> return voidOperand;
    StructureType _ [] -> return voidOperand;
    t -> instruct (LLVM.Phi t [(x, xBlkName), (y, yBlkName)] []);
  };

genCond :: (MonadCodeGen s b m) => Operand -> m Operand;
genCond x = case operandType x of {
  LLVM.PointerType t _ -> instruct $ LLVM.ICmp LLVMIP.EQ x (ConstantOperand $ LLVMC.Null t)  [];
  LLVM.IntegerType w   -> instruct $ LLVM.ICmp LLVMIP.EQ x (ConstantOperand $ LLVMC.Int w 0) [];
};

genPrimOp :: (MonadCodeGen s b m) => PrimOp -> [Operand] -> m Operand;
genPrimOp PrimMul [x, y] = instruct $ LLVM.Mul False False x y [];
genPrimOp PrimDiv [x, y] = instruct $ LLVM.SDiv False x y [];
genPrimOp PrimRem [x, y] = instruct $ LLVM.SRem x y [];
genPrimOp PrimAdd [x, y] = instruct $ case operandType <$> [x, y] of {
  [PointerType _ _, IntegerType _  ] -> LLVM.GetElementPtr False x [y] [];
  [IntegerType _  , PointerType _ _] -> LLVM.GetElementPtr False y [x] [];
  [_, _] -> LLVM.Add False False x y [];
};
genPrimOp PrimSub [x, y] = case operandType <$> [x, y] of {
  [PointerType _ _, IntegerType w  ] ->
    instruct (LLVM.Sub False False (ConstantOperand $ Int w 0) y []) >>= \ y ->
    genPrimOp PrimAdd [x, y];
  [PointerType s _, PointerType t _] | s == t ->
    fromIntegral <$> ML.asks (cgMxnProp ∘ mxnpWordBits) >>= \ w -> size s >>= \ sz ->
    (liftA2 (\ x y -> [x, y]) `on` genCast False (IntegerType w)) x y >>=
    genPrimOp PrimSub >>= \ z -> instruct (LLVM.SDiv True z sz []);
  [_, _] -> instruct $ LLVM.Sub False False x y [];
};
genPrimOp PrimShiftL [x, y] = genCast True (operandType x) y >>= \ y ->
                              instruct $ LLVM.Shl False False x y [];
genPrimOp PrimShiftR [x, y] = genCast True (operandType x) y >>= \ y ->
                              instruct $ LLVM.LShr False x y [];
genPrimOp PrimAnd [x, y] = instruct $ LLVM.And x y [];
genPrimOp PrimOr  [x, y] = instruct $ LLVM.Or  x y [];
genPrimOp PrimXor [x, y] = instruct $ LLVM.Xor x y [];
genPrimOp PrimEq  [x, y] = instruct $ LLVM.ICmp LLVMIP.EQ  x y [];
genPrimOp PrimNEq [x, y] = instruct $ LLVM.ICmp LLVMIP.NE  x y [];
genPrimOp PrimGEq [x, y] = instruct $ LLVM.ICmp LLVMIP.SGE x y [];
genPrimOp PrimLEq [x, y] = instruct $ LLVM.ICmp LLVMIP.SLE x y [];
genPrimOp PrimGÞ  [x, y] = instruct $ LLVM.ICmp LLVMIP.SGT x y [];
genPrimOp PrimLÞ  [x, y] = instruct $ LLVM.ICmp LLVMIP.SLT x y [];

genCast :: (MonadCodeGen s b m) => Bool -> LLVM.Type -> Operand -> m Operand;
genCast signed t x
  | t == operandType x = return x
  | t == VoidType = return voidOperand
  | otherwise =
      fromIntegral <$> ML.asks (cgMxnProp ∘ mxnpWordBits) >>= \ w ->
      case (t, operandType x) of {
        (PointerType VoidType a, _) ->
          genCast signed (PointerType (IntegerType 8) a) x;
        (PointerType _ _, _) ->
          genCast signed (IntegerType w) x >>= \ y -> instruct $ LLVM.IntToPtr y t [];
        (_, PointerType _ _) ->
          instruct (LLVM.PtrToInt x (IntegerType w) []) >>= genCast signed t;
        (IntegerType w2, IntegerType w1) ->
          instruct $ (case compare w1 w2 of { LT -> signed ? LLVM.SExt $ LLVM.ZExt; GT -> LLVM.Trunc; }) x t [];
        _ -> error (show (t, operandType x));
      };




fresh :: (MonadCodeGen s b m) => m Name;
fresh = Name ∘ ("_.tmp" ++) ∘ show <$> ML.askReadModifySTRef cgCountRef (+1);

instruct :: (MonadCodeGen s b m) => Instruction -> m Operand;
instruct ins
  | LLVM.VoidType <- insType ins = voidOperand <$ ML.askModifySTRef cgInsRef (++ [LLVM.Do ins])
  | otherwise =
      fresh >>= \ name ->
      ML.askModifySTRef cgInsRef (++ [name LLVM.:= ins]) >>
      return (LocalReference (insType ins) name)
  ;

terminate :: (MonadCodeGen s b m) => Terminator -> m Name;
terminate trm =
  liftA2 (,) (ML.asks cgThisBlockNameRef >>= readSTRef) (ML.asks cgInsRef >>= readSTRef) >>= \ (blkName, inss) ->
  ML.askModifySTRef cgInsRef (pure []) >>
  blkName <$ ML.askModifySTRef cgBlkRef (++ [BasicBlock blkName inss (LLVM.Do trm)]);




load :: (MonadCodeGen s b m) => Ptr -> m Operand;
load ptr = instruct $ LLVM.Load False ptr Nothing 0 [];

store :: (MonadCodeGen s b m) => Ptr -> Operand -> m ();
store ptr x = void ∘ instruct $ LLVM.Store False ptr x Nothing 0 []; -- waste a name, but ought to not matter

call :: (MonadCodeGen s b m) => Operand -> [Operand] -> m Operand;
call f xs = instruct $ LLVM.Call False LLVM.C [] (Right f)
            (filter (\ (x, _) ->
                     case operandType x of {
                       VoidType -> False;
                       StructureType _ [] -> False;
                       _ -> True;
                     }) (flip (,) [] <$> xs)) [] [];

bitCast :: (MonadCodeGen s b m) => LLVM.Type -> Operand -> m Operand;
bitCast t x = instruct $ LLVM.BitCast x t [];

size :: (MonadCodeGen s b m) => Type -> m Operand;
size t = join $
  liftA2 bitCast
  (IntegerType ∘ fromIntegral <$> ML.asks (cgMxnProp ∘ mxnpWordBits))
  (instruct (LLVM.GetElementPtr False (ConstantOperand $ Null (ptrType t)) [ConstantOperand $ Int 32 1] []));




voidOperand :: Operand;
voidOperand = ConstantOperand (Null LLVM.VoidType);

ptrType :: LLVM.Type -> LLVM.Type;
ptrType = flip PointerType (AddrSpace 0);




lookupSymbol :: (MonadCodeGen s b m) => b -> m Ptr;
lookupSymbol v = Map.lookup v <$> ML.asks cgTerms >>= maybe (ML.asks cgName >>= \ name -> fail ("not in scope: " ++ name v)) return;
