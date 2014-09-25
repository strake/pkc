module Util.LLVM.Type where

import Control.Applicative;
import Data.Ord.Unicode;
import LLVM.General.AST as LLVM;
import LLVM.General.AST.AddrSpace as LLVM;
import LLVM.General.AST.InlineAssembly as LLVMAsm;
import LLVM.General.AST.Constant as LLVMC;
import LLVM.General.AST.Instruction as LLVM;
import LLVM.General.AST.Type as LLVM;
import Util;

operandType :: Operand -> LLVM.Type;
operandType (LocalReference t _) = t;
operandType (ConstantOperand c)  = constType c;

constType :: Constant -> LLVM.Type;
constType (LLVMC.GlobalReference t _) = PointerType t (AddrSpace 0);
constType (LLVMC.Int w _) = IntegerType w;
constType (LLVMC.Null t)  = t;
constType (LLVMC.Undef t) = t;
constType (LLVMC.Struct _ p cs) = StructureType p (constType <$> cs);
constType (LLVMC.BitCast _ t) = t;

insType :: Instruction -> LLVM.Type;
insType (LLVM.Alloca t _ _ _) = PointerType t (AddrSpace 0);
insType (LLVM.Call _ _ _ f _ _ _) = either (error "inline asm unimpl") (operandType & (\ case { PointerType t _ -> t; t -> t; }) & resultType) f;
insType (LLVM.Store _ _ _ _ _ _) = VoidType;
insType (LLVM.Load _ (operandType -> PointerType t _) _ _ _) = t;
insType (LLVM.ExtractValue x [] _) = operandType x;
insType (LLVM.ExtractValue (operandType -> StructureType _ ts) (i:is) _)
  | fromIntegral i ≥ length ts = error "aggregate selector out of range"
  | otherwise = insType (LLVM.ExtractValue (ConstantOperand (Undef (ts !! fromIntegral i))) is []);
insType (LLVM.InsertValue x _ _ _) = operandType x;
insType (LLVM.GetElementPtr _ x is _) = let {
  go :: Operand -> LLVM.Type -> LLVM.Type;
  go _ (PointerType t _) = t;
  go _ (ArrayType _ t) = t;
  go (ConstantOperand (Int _ i)) (StructureType _ ts) = insType (LLVM.ExtractValue (ConstantOperand $ Undef (StructureType False ts)) [fromIntegral i] []);
} in PointerType (foldl (flip go) (operandType x) is) (AddrSpace 0);
insType (LLVM.Mul _ _ x _ _) = operandType x;
insType (LLVM.SDiv _ x _ _) = operandType x;
insType (LLVM.UDiv _ x _ _) = operandType x;
insType (LLVM.SRem x _ _) = operandType x;
insType (LLVM.URem x _ _) = operandType x;
insType (LLVM.Add _ _ x _ _) = operandType x;
insType (LLVM.Sub _ _ x _ _) = operandType x;
insType (LLVM.Shl _ _ x _ _) = operandType x;
insType (LLVM.LShr _ x _ _) = operandType x;
insType (LLVM.AShr _ x _ _) = operandType x;
insType (LLVM.And x _ _) = operandType x;
insType (LLVM.Or  x _ _) = operandType x;
insType (LLVM.Xor x _ _) = operandType x;
insType (LLVM.BitCast _ t _) = t;
insType (LLVM.PtrToInt _ t _) = t;
insType (LLVM.IntToPtr _ t _) = t;
insType (LLVM.Trunc _ t _) = t;
insType (LLVM.ZExt _ t _) = t;
insType (LLVM.SExt _ t _) = t;
insType (LLVM.ICmp _ _ _ _) = IntegerType 1;
insType (LLVM.Phi t _ _) = t;

globalType :: Global -> LLVM.Type;
globalType (Function _ _ _ _ t _ (fmap (\ (Parameter t _ _) -> t) -> ts, va) _ _ _ _ _) = FunctionType t ts va;
globalType (GlobalVariable _ _ _ _ _ _ _ t _ _ _) = t;
globalType (GlobalAlias _ _ _ t _) = t;
