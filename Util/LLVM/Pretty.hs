module Util.LLVM.Pretty where

import Control.Applicative;
import Control.Category.Unicode;
import Data.Bool.Unicode;
import Data.Char;
import Data.Eq.Unicode;
import Data.Maybe;
import Data.Monoid;
import LLVM.General.AST;
import LLVM.General.AST.Attribute;
import LLVM.General.AST.CallingConvention;
import qualified LLVM.General.AST.Constant as C;
import LLVM.General.AST.IntegerPredicate;
import LLVM.General.AST.Linkage;
import LLVM.General.AST.Name;
import LLVM.General.AST.Type;
import LLVM.General.AST.Visibility;
import Text.PrettyPrint.Mainland;
import Util.LLVM.Type;
import Util;

instance Pretty Definition where {
  ppr (GlobalDefinition g) = ppr g;
};

instance Pretty Global where {
  ppr (Function l vis cc retAttributes t name (parms, _) fAttributes m_section align m_gc blks)
    | [] <- blks = text "declare" <+> x
    | otherwise = (stack ∘ concat)
                  [[text "define" <+> x <+> char '{'],
                   ppr <$> blks, [char '}']]
    where {
      x = spread
          [ppr l, ppr vis, ppr cc, spread (ppr <$> retAttributes),
           ppr t, char '@' <> ppr name, tuple (ppr <$> parms),
           mif (align ≠ 0) (text "align" <+> ppr align)];
    };
  ppr (GlobalAlias name l vis t c) =
    spread [char '@' <> ppr name, char '=', ppr vis, text "alias", ppr l, ppr t, ppr c];
  ppr (GlobalVariable name l vis thrLocal _ _ const t m_c m_sect align) =
    spread [char '@' <> ppr name, char '=', ppr l, text (const ? "constant" $ "global"), ppr t,
            maybe mempty ppr m_c, mif (align ≠ 0) (text "align" <+> ppr align)];
};

instance Pretty Linkage where {
  ppr Private = text "private";
  ppr Internal = text "internal";
  ppr External = text "external";
  ppr Weak = text "weak";
};

instance Pretty Visibility where {
  ppr Default = text "default";
};

instance Pretty CallingConvention where {
  ppr C = text "ccc";
  ppr Fast = text "fastcc";
  ppr Cold = text "coldcc";
  ppr GHC = text "cc 10";
  ppr (Numbered n) = text "cc " <+> ppr n;
};

instance Pretty Name where {
  ppr (Name xs) = dquotes (text xs);
  ppr (UnName n) = ppr (fromIntegral n :: Int);
};

instance Pretty ParameterAttribute where {
  ppr Nest = text "nest";
};

instance Pretty Parameter where {
  ppr (Parameter t name attributes) = ppr t <> mconcat ((space <>) ∘ ppr <$> attributes) <+> char '%' <> ppr name;
};

instance Pretty Type where {
  ppr (VoidType) = text "void";
  ppr (IntegerType n) = text "i" <> ppr n;
  ppr (PointerType t _) = ppr t <+> char '*';
  ppr (FunctionType t ts _) = ppr t <+> tuple (ppr <$> ts);
  ppr (StructureType True ts) = angles (ppr (StructureType False ts));
  ppr (StructureType False ts) = (enclose (text "{ ") (text " }") ∘ commasep) (ppr <$> ts);
  ppr (ArrayType n t) = brackets (ppr n <+> char 'x' <+> ppr t);
};

instance Pretty BasicBlock where {
  ppr (BasicBlock name inss trm) = ppr name <> char ':' </> indent 2 (stack (ppr <$> inss) </> ppr trm);
};

instance Pretty a => Pretty (Named a) where {
  ppr (Do x) = ppr x;
  ppr (name := x) = char '%' <> ppr name <+> char '=' <+> ppr x;
};

instance Pretty Instruction where {
  ppr (Add nsw nuw x y _) = text "add" <> mif nuw (text " nuw") <> mif nsw (text " nsw") <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (Sub nsw nuw x y _) = text "sub" <> mif nuw (text " nuw") <> mif nsw (text " nsw") <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (Mul nsw nuw x y _) = text "mul" <> mif nuw (text " nuw") <> mif nsw (text " nsw") <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (SDiv exact x y _) = text "sdiv" <> mif exact (text " exact") <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (UDiv exact x y _) = text "udiv" <> mif exact (text " exact") <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (SRem x y _) = text "srem" <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (URem x y _) = text "urem" <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (Shl nsw nuw x y _) = text "shl" <> mif nuw (text " nuw") <> mif nsw (text " nsw") <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (LShr exact x y _) = text "lshr" <> mif exact (text " exact") <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (AShr exact x y _) = text "ashr" <> mif exact (text " exact") <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (And x y _) = text "and" <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (Or  x y _) = text "or " <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (Xor x y _) = text "xor" <+> ppr (operandType x) <+> commasep (ppr <$> [x, y]);
  ppr (ExtractValue x is _) = text "extractvalue" <+> commasep ((ppr (operandType x) <+> ppr x) : (ppr <$> is));
  ppr (InsertValue x y is _) = text "insertvalue" <+> commasep ((ppr (operandType x) <+> ppr x) :
                                                                (ppr (operandType y) <+> ppr y) : (ppr <$> is));
  ppr (GetElementPtr inbounds p is _) = text "getelementptr " <> mif inbounds (text "inbounds ") <>
                                        commasep ((\ x -> ppr (operandType x) <+> ppr x) <$> p:is);
  ppr (Alloca t m_n align _) = text "alloca" <+> ppr t <> maybe (text " ") (\ n -> char ',' <+> ppr (operandType n) <+> ppr n) m_n <>
                               mif (align ≠ 0) (text ", align" <+> ppr align);
  ppr (Load vol p m_atom align _) = text "load" <> mif vol (text " volatile") <+> ppr (operandType p) <+> ppr p;
  ppr (Store vol p x m_atom align _) = text "store" <> mif vol (text " volatile") <+>
                                       ppr (operandType x) <+> ppr x <> char ',' <+> ppr (operandType p) <+> ppr p;
  ppr (Call tail cc rAttributes f args fAttributes _) =
    mif tail (text "tail ") <> text "call" <+>
    ppr cc <> mconcat ((space <>) ∘ ppr <$> rAttributes) <+>
    either (error "inline asm unimpl") (operandType & (\ case { PointerType t _ -> t; t -> t; }) & resultType & ppr) f <+>
    either (error "inline asm unimpl") ppr f <+> tuple (liftA2 (<+>) (ppr ∘ operandType) ppr ∘ fst <$> args);
  ppr (BitCast x t _) = text "bitcast" <+> ppr (operandType x) <+> ppr x <+> text "to" <+> ppr t;
  ppr (PtrToInt x t _) = text "ptrtoint" <+> ppr (operandType x) <+> ppr x <+> text "to" <+> ppr t;
  ppr (IntToPtr x t _) = text "inttoptr" <+> ppr (operandType x) <+> ppr x <+> text "to" <+> ppr t;
  ppr (Trunc x t _) = text "trunc" <+> ppr (operandType x) <+> ppr x <+> text "to" <+> ppr t;
  ppr (SExt x t _) = text "sext" <+> ppr (operandType x) <+> ppr x <+> text "to" <+> ppr t;
  ppr (ZExt x t _) = text "zext" <+> ppr (operandType x) <+> ppr x <+> text "to" <+> ppr t;
  ppr (ICmp p x y _) = text "icmp" <+> ppr p <+> ppr (operandType x) <+> ppr x <> char ',' <+> ppr y;
  ppr (Phi t as _) = text "phi" <+> ppr t <+> commasep ((\ (x, v) -> brackets (ppr x <> text ", %" <> ppr v)) <$> as);
};

instance Pretty Terminator where {
  ppr (Ret m_x _) = text "ret" <> maybe mempty (\ x -> char ' ' <> case operandType x of { VoidType -> text "void"; t -> ppr t <+> ppr x; }) m_x;
  ppr (CondBr p x y _) = text "br i1" <+> commasep (ppr p : (((text "label %" <>) ∘ ppr) <$> [x, y]));
  ppr (Br x _) = text "br label %" <> ppr x;
  ppr (Unreachable _) = text "unreachable";
};

instance Pretty Operand where {
  ppr (LocalReference _ name) = char '%' <> ppr name;
  ppr (ConstantOperand c) = ppr c;
};

instance Pretty C.Constant where {
  ppr (C.Int w n) = ppr n;
  ppr (C.Null t) = text "null";
  ppr (C.Undef t) = text "undef";
  ppr (C.GlobalReference t name) = char '@' <> ppr name;
  ppr (C.BitCast c t) = text "bitcast" <+> parens (ppr (constType c) <+> ppr c <+> text "to" <+> ppr t);
  ppr (C.Struct m_name True cs) = angles (ppr (C.Struct m_name False cs));
  ppr (C.Struct _ False cs) = (enclose (text "{ ") (text " }") ∘ commasep) (liftA2 (<+>) (ppr ∘ constType) ppr <$> cs);
};

instance Pretty IntegerPredicate where {
  ppr = text ∘ fmap toLower ∘ show;
};

mif True  x = x;
mif False _ = mempty;
