module CodeGen where

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
import Data.Syntax as S;
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
import Util.Lens;
import Util.Lens.Monadic as ML;
import Util.LLVM.Type;
import CodeGen.Common;

genDecls :: (MonadCodeGen s b m) => [(S.Decl b, Linkage, Mutability, S.Type b, Maybe (S.Expr b))] -> m [LLVM.Definition];
genDecls =
  let {
    genDecl' :: (MonadCodeGen s b m) => (S.Decl b, Linkage, Mutability, S.Type b, Maybe (S.Expr b)) -> m LLVM.Global;
    genDecl' (VarDecl v, l, mut, t, m_x) =
      liftA3
      (\ name τ m_c -> GlobalVariable name l LLVMV.Default False (AddrSpace 0) False (not mut) τ m_c Nothing 0)
      (Name ∘ ($ v) <$> ML.asks cgName) (genType t)
      (traverse (fmap (fromMaybe (error "non-constant at top level")) ∘ genConstExpr) m_x);
    genDecl' (FuncDecl v parm@(pruneUnits -> m_parm), l, False, t, m_x) =
      traverse (genType ∘ parmType) m_parm >>= \ m_σ ->
      liftA3
      (\ name τ body -> Function l LLVMV.Default LLVM.C [] τ name (maybe [] (\ σ -> [Parameter σ (Name "_.arg") []]) m_σ, False) [] Nothing 0 Nothing body)
      (Name ∘ ($ v) <$> ML.asks cgName) (genType t)
      (maybe (return [])
       (\ x ->
        (ML.localM cgCountRef (pure $ newSTRef 0) &
         ML.localM (tripleLens cgInsRef cgBlkRef cgThisBlockNameRef) (pure $ liftA3 (,,) (newSTRef []) (newSTRef []) (newSTRef (Name "_.entry"))))
        (traverse (return *=* genType) parm >>=
         foldrM (\ case {
                   (Just v, τ) -> \ m -> (\ π -> Map.insert v π m) <$> instruct (Alloca τ Nothing 0 []);
                   _ -> return;
                 }) Map.empty >>= \ m ->
         ML.local cgTerms (Map.union m) $
         maybe (return ()) (\ σ -> genAssign (parmExpr parm) (LocalReference σ (Name "_.arg"))) m_σ >>
         genExpr x >>= \ χ -> terminate (Ret (Just χ) []) >> ML.asks cgBlkRef >>= readSTRef))
       m_x);

    pruneUnits :: LTree [] a -> Maybe (LTree [] a);
    pruneUnits (Stem (mapMaybe pruneUnits -> ts))
      | [] <- ts = Nothing
      | otherwise = Just (Stem ts)
      ;
    pruneUnits t = Just t;
  } in \ ds ->
  foldrM (\ (decl,_,_,t,_) m ->
          liftA2 (\ τ name -> Map.insert (declName decl) (τ, name) m)
          (genDeclType decl t) (Name ∘ ($ declName decl) <$> ML.asks cgName)) Map.empty ds >>= \ m ->
  (fmap snd ∘ M.listens _cgDefns ∘ ML.local cgTerms (Map.union $ uncurry GlobalReference & ConstantOperand <$> m))
  (traverse (fmap LLVM.GlobalDefinition ∘ genDecl') ds >>= ML.tells cgDefns);

genDeclType :: (MonadCodeGen s b m) => S.Decl b -> S.Type b -> m LLVM.Type;
genDeclType (VarDecl _) = genType;
genDeclType (FuncDecl _ s) = genType >=> \ τ -> (\ σ -> LLVM.FunctionType τ [σ] False) <$> genType (parmType s);

genConstExpr :: (MonadCodeGen s b m) => S.Expr b -> m (Maybe LLVMC.Constant);
genConstExpr (S.Literal l) = return ∘ Just $ genLiteral l;
genConstExpr (S.Tuple xs) = (fmap ∘ fmap) (LLVMC.Struct Nothing False) $ ((fmap ∘ fmap) sequenceA ∘ traverse) genConstExpr xs;
genConstExpr (S.Ptr (Var v)) = (\ case { ConstantOperand c -> Just c; _ -> Nothing; }) <$> askLookupNameCGM cgTerms v;
genConstExpr _ = return Nothing;

genExpr :: (MonadCodeGen s b m) => S.Expr b -> m Operand;
genExpr =
  let {
    g :: (MonadCodeGen s b m) => S.Expr b -> m Operand;
    g (S.Var v) = askLookupNameCGM cgTerms v >>= load;
    g (S.Ptr (Var v)) = askLookupNameCGM cgTerms v;
    g (S.Follow x) = genExpr x >>= load;
    g (S.Call f x) = join $ liftA2 call (genExpr (S.Ptr f)) (pure <$> genExpr x);
    g (S.Tuple xs) = traverse genExpr xs >>= \ χs ->
      foldrM (\ (ii, χ) α -> instruct (LLVM.InsertValue α χ [ii] []))
      (ConstantOperand (Undef $ StructureType False (operandType <$> χs)))
      (zip [0..] χs);
    g (S.Conj x y) = genExpr x >>= \ χ -> genIf (return χ) (genExpr y) (return χ);
    g (S.Disj x y) = genExpr x >>= \ χ -> genIf (return χ) (return χ) (genExpr y);
    g (S.If p x y) = genIf (genExpr p) (genExpr x) (genExpr y);
    g (S.PrimOp op xs) = traverse genExpr xs >>= genPrimOp op;
    g (S.Cast t x) = join $ liftA2 (genCast (case t of { IntegralType True -> True; _ -> False; })) (genType t) (genExpr x);
    g (y S.:= x) = voidOperand <$ (genExpr x >>= genAssign y);
    g (S.With tm x) =
      traverse (genType >=> \ τ -> instruct (LLVM.Alloca τ Nothing 0 [])) tm >>= \ m ->
      ML.local cgTerms (Map.union m) (genExpr x);
    g (S.Then x y) = genExpr x >> genExpr y;
    g (S.Loop p x y) = voidOperand <$ genLoop (genExpr p) (genExpr x) (genExpr y);
    g (S.Return m_x) =
      traverse genExpr m_x >>= \ m_χ ->
      voidOperand <$ (terminate (LLVM.Ret m_χ []) >> ML.askWriteSTRefM cgThisBlockNameRef fresh);
  }
  in \ x -> genConstExpr x >>= \ m_c ->
  case m_c of {
    Just c -> return (ConstantOperand c);
    Nothing -> g x;
  };

genAssign :: (MonadCodeGen s b m) => S.Expr b -> Operand -> m ();
genAssign (S.Var v) χ = askLookupNameCGM cgTerms v >>= flip store χ;
genAssign (S.Tuple xs) χ = fold <$> zipWithA (\ ii x -> instruct (LLVM.ExtractValue χ [ii] []) >>= genAssign x) [0..] xs;
genAssign (S.Follow x) χ = genExpr x >>= flip store χ;

genLiteral :: S.Literal -> Constant;
genLiteral (LInteger n) = LLVMC.Int 64 n;
genLiteral (LTuple ls) = LLVMC.Struct Nothing False (genLiteral <$> ls);

genType :: (MonadCodeGen s b m) => S.Type b -> m LLVM.Type;
genType (S.PtrType t) = ptrType <$> genType t;
genType (S.TupleType []) = return LLVM.VoidType;
genType (S.TupleType ts) = LLVM.StructureType False <$> traverse genType ts;
genType (S.FuncType x y) = liftA3 LLVM.FunctionType (genType y) (filter (≠ LLVM.VoidType) <$> traverse genType [x]) (pure False);
genType (S.Typlication (S.NamedType v) (S.TypeInteger w)) =
  askLookupNameCGM cgTypes v >>= \ case {
    IntegralType _ -> return (LLVM.IntegerType (fromIntegral w));
    _ -> error "bad typlication";
  };
genType (S.IntegralType _) = LLVM.IntegerType ∘ fromIntegral <$> ML.asks (cgMxnProp ∘ mxnpWordBits);
genType (S.NamedType v) = askLookupNameCGM cgTypes v >>= genType;
