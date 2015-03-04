module CodeGen where

import Prelude hiding (foldr, any);

import Control.Applicative;
import Control.Arrow;
import Control.Category.Unicode;
import Control.Monad.Base;
import Control.Monad.Except;
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
import Data.Functor2;
import Data.Lens as L;
import qualified Data.List as List;
import Data.LTree;
import Data.Map (Map);
import qualified Data.Map as Map;
import Data.Set (Set);
import qualified Data.Set as Set;
import Data.Maybe;
import Data.Syntax as S;
import Data.Tag;
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
import TypChk;

genDecls :: ∀ α β γ a b c m s . (MonadCodeGen s a b m) => Lens α β (TagT (S.Type a) () b) c -> [(S.Decl a α b, Linkage, Mutability, TagT (S.Type a) γ b, Maybe (TagT (S.Expr a) α b))] -> m [LLVM.Definition];
genDecls l =
  let {
    genDecl' :: (MonadCodeGen s a b m) => (S.Decl a α b, Linkage, Mutability, TagT (S.Type a) γ b, Maybe (TagT (S.Expr a) α b)) -> m LLVM.Global;
    genDecl' (VarDecl v, link, mut, t, m_x) =
      liftA3
      (\ name τ m_c -> GlobalVariable name link LLVMV.Default False (AddrSpace 0) False (not mut) τ m_c Nothing 0)
      (Name ∘ ($ v) <$> ML.asks cgName) (genType t)
      (traverse (fmap (fromMaybe (error "non-constant at top level")) ∘ genConstExpr l) m_x);
    genDecl' (FuncDecl v parm@(pruneUnits -> m_parm), link, False, t, m_x) =
      traverse (genType ∘ parmType ∘ fmap (id *** fmap2 (pure ()))) m_parm >>= \ m_σ ->
      liftA3
      (\ name τ body -> Function link LLVMV.Default LLVM.C [] τ name (maybe [] (\ σ -> [Parameter σ (Name "_.arg") []]) m_σ, False) [] Nothing 0 Nothing body)
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
         maybe (return ()) (\ σ -> genAssignMaybe id (parmExpr ((id *** fmap2 (pure ())) <$> parm)) (LocalReference σ (Name "_.arg"))) m_σ >>
         genExpr l x >>= \ χ -> terminate (Ret (Just χ) []) >> ML.asks cgBlkRef >>= readSTRef))
       m_x);

    pruneUnits :: ∀ a . LTree [] a -> Maybe (LTree [] a);
    pruneUnits (Stem (mapMaybe pruneUnits -> ts))
      | [] <- ts = Nothing
      | otherwise = Just (Stem ts)
      ;
    pruneUnits t = Just t;
  } in \ ds ->
  let {
    m = foldr (\ (decl,_,_,t,_) -> Map.insert (declName decl) (declType (fmap2 (pure ()) decl) (fmap2 (pure ()) t))) Map.empty ds;
  } in
  fmap snd ∘ M.listens _cgDefns ∘
  ML.localM cgTerms (ap
                     (Map.union <$>
                      Map.traverseWithKey
                      (\ v t ->
                       ConstantOperand <$>
                       liftA2 GlobalReference (genType t) (Name ∘ ($ v) <$> ML.asks cgName))
                     m) ∘ return) $
  traverse (fmap LLVM.GlobalDefinition ∘ genDecl') ds >>= ML.tells cgDefns;

genConstExpr :: (MonadCodeGen s a b m) => Lens α β (TagT (S.Type a) () b) c -> TagT (S.Expr a) α b -> m (Maybe LLVMC.Constant);
genConstExpr l (TagT (L.get l -> t) x) = case x of {
  S.Literal l -> return ∘ Just $ genLiteral l;
  S.Tuple xs -> (fmap ∘ fmap) (LLVMC.Struct Nothing False) $ ((fmap ∘ fmap) sequenceA ∘ traverse) (genConstExpr l) xs;
  S.Ptr (TagT _ (Var v)) -> (\ case { ConstantOperand c -> Just c; _ -> Nothing; }) <$> askLookupNameCGM cgTerms v;
  _ -> return Nothing;
};

genExpr :: (MonadCodeGen s a b m) => Lens α β (TagT (S.Type a) () b) c -> TagT (S.Expr a) α b -> m Operand;
genExpr l (TagT n x) = genConstExpr l (TagT n x) >>= \ case {
  Just c -> return (ConstantOperand c);
  Nothing -> case x of {
    S.Var v -> askLookupNameCGM cgTerms v >>= load;
    S.Ptr (TagT _ (Var v)) -> askLookupNameCGM cgTerms v;
    S.Follow x -> genExpr l x >>= load;
    S.Call f@(TagT m _) x -> join $ liftA2 call (genExpr l (TagT m (S.Ptr f))) (pure <$> genExpr l x);
    S.Tuple xs -> unzip <$> traverse (genExpr l &=& genType ∘ L.get l ∘ tag) xs >>= \ (χs, τs) ->
      foldrM (\ (ii, χ) α -> instruct (LLVM.InsertValue α χ [ii] []))
      (ConstantOperand (Undef $ StructureType False τs))
      (zip [0..] χs);
    S.Member x (Left (fmap (+ negate 1) -> kt)) -> genExpr l x >>= \ χ ->
      let {
        go (Leaf k) = instruct (LLVM.ExtractValue χ [fromIntegral k] []);
        go (Stem ts) =
          foldrM
          (\ (ii, kt) α -> go kt >>= \ υ -> instruct (LLVM.InsertValue α υ [ii] []))
          (ConstantOperand (Undef $ let { LLVM.StructureType _ τs = operandType χ; } in ltree id (StructureType False) $ (τs !!) <$> kt))
          (zip [0..] ts);
      } in go kt;
    S.Conj x y -> genExpr l x >>= \ χ -> genIf (return χ) (genExpr l y) (return χ);
    S.Disj x y -> genExpr l x >>= \ χ -> genIf (return χ) (return χ) (genExpr l y);
    S.If p x y -> genIf (genExpr l p) (genExpr l x) (genExpr l y);
    S.PrimOp op xs -> traverse (genExpr l) xs >>= genPrimOp op;
    S.Cast t x -> join $ liftA2 (genCast (case unTagT t of { IntegralType True -> True; _ -> False; })) (genType t) (genExpr l x);
    y S.:= x -> voidOperand <$ (genExpr l x >>= genAssign l y);
    S.With tm x ->
      traverse (genType >=> \ τ -> instruct (LLVM.Alloca τ Nothing 0 [])) tm >>= \ m ->
      ML.local cgTerms (Map.union m) (genExpr l x);
    S.Then x y -> genExpr l x >> genExpr l y;
    S.Loop p x y -> voidOperand <$ genLoop (genExpr l p) (genExpr l x) (genExpr l y);
    S.Return m_x ->
      traverse (genExpr l) m_x >>= \ m_χ ->
      voidOperand <$ (terminate (LLVM.Ret m_χ []) >> ML.askWriteSTRefM cgThisBlockNameRef fresh);
  };
};

genAssign :: (MonadCodeGen s a b m) => Lens α β (TagT (S.Type a) () b) c -> TagT (S.Expr a) α b -> Operand -> m ();
genAssign l (TagT n x) χ = case x of {
  S.Var v    -> askLookupNameCGM cgTerms v >>= flip store χ;
  S.Tuple xs -> fold <$> zipWithA (\ ii x -> instruct (LLVM.ExtractValue χ [ii] []) >>= genAssign l x) [0..] xs;
  S.Follow x -> genExpr l x >>= flip store χ;
};

genAssignMaybe :: (MonadCodeGen s a b m) => Lens α β (TagT (S.Type a) () b) c -> TagT (S.Expr a) α (Maybe b) -> Operand -> m ();
genAssignMaybe l (TagT n x) χ = case x of {
  S.Var Nothing -> return ();
  S.Var (Just v) -> askLookupNameCGM cgTerms v >>= flip store χ;
  S.Tuple xs -> fold <$> zipWithA (\ ii x -> instruct (LLVM.ExtractValue χ [ii] []) >>= genAssignMaybe l x) [0..] xs;
};

genLiteral :: S.Literal -> Constant;
genLiteral (LInteger n) = LLVMC.Int 64 n;
genLiteral (LTuple ls) = LLVMC.Struct Nothing False (genLiteral <$> ls);

genType :: (MonadCodeGen s a b m) => TagT (S.Type a) α b -> m LLVM.Type;
genType (TagT n x) = case x of {
  S.PtrType t -> ptrType <$> genType t;
  S.TupleType [] -> return LLVM.VoidType;
  S.TupleType ts -> LLVM.StructureType False <$> traverse genType ts;
  S.FuncType x y -> liftA3 LLVM.FunctionType (genType y) (filter (≠ LLVM.VoidType) <$> traverse genType [x]) (pure False);
  S.Typlication (TagT _ (S.IntegralType _)) (TagT _ (S.TypeInteger w)) -> return (LLVM.IntegerType (fromIntegral w));
  S.Typlication (TagT _ (S.NamedType v)) (fmap2 (pure ()) -> t) -> askLookupNameCGM cgTypes v >>= \ s -> genType (TagT () (S.Typlication s t));
  S.IntegralType _ -> LLVM.IntegerType ∘ fromIntegral <$> ML.asks (cgMxnProp ∘ mxnpWordBits);
  S.NamedType v -> askLookupNameCGM cgTypes v >>= genType;
  S.StructType ms -> genType (TagT n (S.TupleType (snd <$> ms))); -- code already destructed
};
