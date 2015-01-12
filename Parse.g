module Parse where

import Control.Applicative;
import Control.Category.Unicode;
import Control.Monad.Except;
import Control.Monad.State;
import Control.Monad.State.Lens as ML;
import Data.LTree;
import Data.List as List;
import Data.Map (Map);
import qualified Data.Map as Map;
import Data.Maybe;
import Data.Monoid;
import Data.PrimOp;
import Data.Syntax;
import Data.Tag;
import Data.Text.Pos;
import Data.Token;
import Data.Linkage as L;
import Lex;

%{

Terminal	= *EOF
		| LParenth as '(' | RParenth as ')'
		| LBracket as '[' | RBracket as ']'
		| LBrace   as '{' | RBrace   as '}'
		| SemiColon as ';' | Comma as ','

		| KeyWord "_"		as "_"

		| KeyWord "with"	as "with"
		| KeyWord "for"		as "for"
		| KeyWord "return"	as "return"

		| KeyWord "@"		as "@"
		| KeyWord "*"		as "*"
		| KeyWord "."		as "."
		| KeyWord ":"		as ":"
		| KeyWord "≔"		as "≔"

		| IntegerLiteral { Integer } as "<integer>"

		| TermName { [Char] }
		| TypeName { [Char] }

		| Symbol "->"

		| Symbol "?!"
		| Symbol "&&"
		| Symbol "="
		| Symbol "≠"
		| Symbol "≥"
		| Symbol "≤"
		| Symbol ">"
		| Symbol "<"
		| Symbol "∧"
		| Symbol "∨"
		| Symbol "⊻"
		| Symbol "⊼"
		| Symbol "⊽"
		| Symbol "<<"
		| Symbol ">>"
		| Symbol "<<<"
		| Symbol ">>>"
		| Symbol "+"
		| Symbol "-"
		| Symbol "×"
		| Symbol "/"

		| Symbol "¬"

		| Symbol "?" | Symbol "!"

		| Symbol "∧="
		| Symbol "∨="
		| Symbol "⊻="
		| Symbol "⊼="
		| Symbol "⊽="
		| Symbol "+="
		| Symbol "-="
		| Symbol "×="
		| Symbol "/="
		| Symbol "<<="
		| Symbol ">>="
		| Symbol "<<<="
		| Symbol ">>>="
		;

left  2 Symbol "?!";
left  3 Symbol "&&";
left  4 Symbol "=";
left  4 Symbol "≠";
left  4 Symbol "≥";
left  4 Symbol "≤";
left  4 Symbol ">";
left  4 Symbol "<";
left  5 Symbol "∧";
left  5 Symbol "∨";
left  5 Symbol "⊻";
left  5 Symbol "⊼";
left  5 Symbol "⊽";
left  6 Symbol "<<";
left  6 Symbol ">>";
left  6 Symbol "<<<";
left  6 Symbol ">>>";
left  7 Symbol "+";
left  7 Symbol "-";
left  8 Symbol "×";
left  8 Symbol "/";

top		{ [(Decl CTR [Char], Linkage, Mutability, TagT CTR Type [Char], Maybe (TagT CTR Expr [Char]))] };
top		{ ds }							: sepEndBy topDecl ';' { ds };

topDecl		{ (Decl CTR [Char], Linkage, Mutability, TagT CTR Type [Char], Maybe (TagT CTR Expr [Char])) };
topDecl		{ (VarDecl v, L.External, True,  t, Nothing) }		: termName { v }, ":", type { t };
topDecl		{ (VarDecl v, L.External, True,  t, Just x) }		: termName { v }, ":", type { t }, "≔", expr { x };
topDecl		{ (FuncDecl v parm, L.External, False, t, Nothing) }	: termName { v }, parm { parm }, ":", type { t };
topDecl		{ (FuncDecl v parm, L.External, False, t, Just x) }	: termName { v }, parm { parm }, ":", type { t }, "≔", expr { x };

parm		{ LTree [] (Maybe [Char], TagT CTR Type [Char]) };
parm		{ stlist id Stem parm }					: '(', sepBy parm ',' { parm }, ')';
parm		{ Leaf (Just v, t) }					: termName { v }, ":", type { t };
parm		{ Leaf (Nothing, t) }					: "_", ":", type { t };

expr		{ TagT CTR Expr [Char] };
expr		{ x }							: expr7 { x };

expr0_		{ Expr CTR [Char] };
expr0_		{ stlist unTagT Tuple xs }				: '(', sepBy expr ',' { xs }, ')';
expr0_		{ unTagT $
		  foldr (liftTagT2 Then)
		  (fromMaybe (TagT mempty $ Tuple []) m_x) (x:xs) }	: '(', expr { x }, ';', sepEndBy expr ';' { xs }, opt expr { m_x }, ')';
expr0_		{ Struct (Map.fromList ms) }				: '{', sepMayEndBy termMember ',' { ms }, '}';
expr0_		{ Var v }						: termName { v };
expr0_		{ Literal (LInteger n) }				: IntegerLiteral { n };

termMember	{ ([Char], TagT CTR Expr [Char]) };
termMember	{ (v, x) }						: ".", termName { v }, "≔", expr { x };

expr0		{ TagT CTR Expr [Char] };
expr0		{ TagT loc x }						: locate expr0_ { (loc, x) };

expr1		{ TagT CTR Expr [Char] };
expr1		{ x }							: expr0 { x };
expr1		{ TagT (a :–: b) $ Member x sel }			: expr1 { x@(TagT (a :–: _) _) }, ".", locate selector { (_ :–: b, sel) };

selector	{ Either (LTree [] Int) (LTree [] [Char]) };
selector	{ Left  kt }						: deepNest "<integer>" '(' ',' ')' { fmap fromIntegral -> kt };
selector	{ Right vt }						: deepNest termName '(' ',' ')' { vt };

expr2a		{ TagT CTR Expr [Char] };
expr2a		{ x }							: expr1 { x };
expr2a		{ liftTagT2 Call f x }					: expr2a { f }, expr1 { x };

expr2b		{ TagT CTR Expr [Char] };
expr2b		{ TagT (a :–: b) $ Return m_x }				: pos { a }, "return", opt expr1 { m_x }, pos { b };

expr2		{ TagT CTR Expr [Char] };
expr2		{ x }							: expr2a { x };
expr2		{ x }							: expr2b { x };

expr3		{ TagT CTR Expr [Char] };
expr3		{ x }							: expr2 { x };
expr3		{ TagT (a :–: b) $ Follow x }				: pos { a }, "*", expr3 { x@(TagT (_ :–: b) _) };
expr3		{ TagT (a :–: b) $ PrimOp PrimNeg [x] }			: pos { a }, Symbol "¬", expr3 { x@(TagT (_ :–: b) _) };

expr4		{ TagT CTR Expr [Char] };
expr4		{ x }							: expr3 { x };
expr4		{ liftTagT2 Conj x y }					: expr4 { x }, Symbol "&&", expr4 { y };
expr4		{ liftTagT2 Disj x y }					: expr4 { x }, Symbol "?!", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "=") x y }			: expr4 { x }, Symbol "=", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "≠") x y }			: expr4 { x }, Symbol "≠", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "≥") x y }			: expr4 { x }, Symbol "≥", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "≤") x y }			: expr4 { x }, Symbol "≤", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp ">") x y }			: expr4 { x }, Symbol ">", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "<") x y }			: expr4 { x }, Symbol "<", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "∧") x y }			: expr4 { x }, Symbol "∧", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "∨") x y }			: expr4 { x }, Symbol "∨", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "⊻") x y }			: expr4 { x }, Symbol "⊻", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "⊼") x y }			: expr4 { x }, Symbol "⊼", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "⊽") x y }			: expr4 { x }, Symbol "⊽", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "<<<") x y }			: expr4 { x }, Symbol "<<<", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp ">>>") x y }			: expr4 { x }, Symbol ">>>", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "<<") x y }			: expr4 { x }, Symbol "<<", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp ">>") x y }			: expr4 { x }, Symbol ">>", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "+") x y }			: expr4 { x }, Symbol "+", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "-") x y }			: expr4 { x }, Symbol "-", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "×") x y }			: expr4 { x }, Symbol "×", expr4 { y };
expr4		{ liftTagT2 (lookupBinOp "/") x y }			: expr4 { x }, Symbol "/", expr4 { y };

expr5		{ TagT CTR Expr [Char] };
expr5		{ x }							: expr4 { x };
expr5		{ liftTagT3 If p x y }					: expr5 { p }, Symbol "?", expr5 { x }, Symbol "!", expr5 { y };

expr6		{ TagT CTR Expr [Char] };
expr6		{ x }							: expr5 { x };
expr6		{ liftTagT2 Cast t x }					: expr6 { x }, ":", type { t };

expr7		{ TagT CTR Expr [Char] };
expr7		{ x }							: expr6 { x };
expr7		{ TagT (a :–: b) $ With (Map.fromList ds) x }		: pos { a }, KeyWord "with", '(', sepMayEndBy localDecl ',' { ds }, ')', expr7 { x@(TagT (_ :–: b) _) };
expr7		{ liftTagT2 (:=) y (liftTagT2 (lookupBinOp opv) y x) }	: expr6 { y }, assignOp { opv }, expr7 { x };
expr7		{ liftTagT3 Loop p x y }				: "for", expr1 { p }, expr1 { x }, expr { y };

localDecl	{ ([Char], TagT CTR Type [Char]) };
localDecl	{ (v, t) }						: termName { v }, ":", type { t };

atype_		{ Type CTR [Char] };
atype_		{ NamedType v }						: TypeName { v };
atype_		{ stlist unTagT TupleType ts }				: '(', sepBy type ',' { ts }, ')';
atype_		{ StructType ms }					: '{', sepMayEndBy typeMember ',' { ms }, '}';
atype_		{ TypeInteger n }					: "<integer>" { n };

atype		{ TagT CTR Type [Char] };
atype		{ TagT loc x }						: locate atype_ { (loc, x) };

ptype		{ TagT CTR Type [Char] };
ptype		{ t }							: atype { t };
ptype		{ liftTagT2 Typlication s t }				: ptype { s }, atype { t };

qtype		{ TagT CTR Type [Char] };
qtype		{ t }							: ptype { t };
qtype		{ TagT (a :–: b) $ PtrType t }				: qtype { t@(TagT (a :–: _) _) }, "*", pos { b };

type		{ TagT CTR Type [Char] };
type		{ t }							: qtype { t };
type		{ liftTagT2 FuncType t s }				: type { t }, Symbol "->", qtype { s };

typeMember	{ (Maybe [Char], TagT CTR Type [Char]) };
typeMember	{ (Just v,  t) }					: termName { v }, ":", type { t };
typeMember	{ (Nothing, t) }					: "_", ":", type { t };

assignOp	{ [Char] };
assignOp	{ "" }							: "≔";
assignOp	{ "∧" }							: Symbol "∧=";
assignOp	{ "∨" }							: Symbol "∨=";
assignOp	{ "⊻" }							: Symbol "⊻=";
assignOp	{ "⊼" }							: Symbol "⊼=";
assignOp	{ "⊽" }							: Symbol "⊽=";
assignOp	{ "+" }							: Symbol "+=";
assignOp	{ "-" }							: Symbol "-=";
assignOp	{ "×" }							: Symbol "×=";
assignOp	{ "/" }							: Symbol "/=";
assignOp	{ "<<" }						: Symbol "<<=";
assignOp	{ ">>" }						: Symbol ">>=";
assignOp	{ "<<<" }						: Symbol "<<<=";
assignOp	{ ">>>" }						: Symbol ">>>=";

termName	{ [Char] };
termName	{ v }							: TermName { v };

sepEndBy x s { [a] } <- x { a }, s;
sepEndBy x s { [] }		:;
             { xs ++ [x] }	| sepEndBy x s { xs }, x { x }, s;

sepMayEndBy x s { [a] } <- x { a }, s;
sepMayEndBy x s { [] }		:;
                { xs ++ [x] }	| sepEndBy x s { xs }, x { x }, opt s; 

deepNest x r s t { LTree [] a } <- x { a }, r, s, t;
deepNest x r s t { Leaf x }		: x { x };
                 { stlist id Stem ts }	| r, deepNests x r s t { ts }, t;
--                 frown fails on this
--                 { stlist id Stem ts }	| r, sepBy (deepNest x r s t) s { ts }, t;

deepNests x r s t { [LTree [] a] } <- x { a }, r, s, t;
deepNests x r s t { [] }	:;
                  { [t] }       | deepNest x r s t { t };
                  { ts ++ [t] }	| deepNests x r s t { ts }, s, deepNest x r s t { t };

locate x { (CTR, a) } <- x { a };
locate x { (a :–: b, x) }	: pos { a }, x { x }, pos { b };

pos { TextPos };
pos {% ML.gets lexPos }		:;
}%

frownScan = Lex.scan1M "scan failure";

frown t = ML.gets lexPos >>= \ pos -> throwError ("parse failure at " ++ show pos ++ ": got " ++ show t);

stlist :: (a -> b) -> ([a] -> b) -> [a] -> b;
stlist f g [x] = f x;
stlist f g  xs = g xs;

type CTR = ConvexTextRange;

lookupBinOp :: [Char] -> TagT CTR Expr [Char] -> TagT CTR Expr [Char] -> Expr CTR [Char];
lookupBinOp "" _ (TagT _ y) = y;
lookupBinOp "=" x y = PrimOp PrimEq  [x, y];
lookupBinOp "≠" x y = PrimOp PrimNEq [x, y];
lookupBinOp "≥" x y = PrimOp PrimGEq [x, y];
lookupBinOp "≤" x y = PrimOp PrimLEq [x, y];
lookupBinOp ">" x y = PrimOp PrimGÞ  [x, y];
lookupBinOp "<" x y = PrimOp PrimLÞ  [x, y];
lookupBinOp "∧" x y = PrimOp PrimAnd [x, y];
lookupBinOp "∨" x y = PrimOp PrimOr  [x, y];
lookupBinOp "⊻" x y = PrimOp PrimXor [x, y];
lookupBinOp "⊼" x y =
  (PrimOp PrimXor ∘ fmap (TagT mempty))
  [PrimOp PrimAnd [x, y],
   Literal (LInteger (negate 1))];
lookupBinOp "⊽" x y =
  (PrimOp PrimXor ∘ fmap (TagT mempty))
  [PrimOp PrimOr [x, y],
   Literal (LInteger (negate 1))];
lookupBinOp "<<" x y = PrimOp PrimShiftL [x, y];
lookupBinOp ">>" x y = PrimOp PrimShiftR [x, y];
lookupBinOp "<<<" x y = PrimOp PrimRotL [x, y];
lookupBinOp ">>>" x y = PrimOp PrimRotR [x, y];
lookupBinOp "+" x y = PrimOp PrimAdd [x, y];
lookupBinOp "-" x y = PrimOp PrimSub [x, y];
lookupBinOp "×" x y = PrimOp PrimMul [x, y];
lookupBinOp "/" x y = PrimOp PrimDiv [x, y];

liftTagT2 :: (Monoid tag) => (TagT tag r a -> TagT tag s b -> t tag c) -> TagT tag r a -> TagT tag s b -> TagT tag t c;
liftTagT2 f xt@(TagT s x) yt@(TagT t y) = TagT (s <> t) (f xt yt);

liftTagT3 :: (Monoid tag) => (TagT tag s a -> TagT tag t b -> TagT tag u c -> v tag d) -> TagT tag s a -> TagT tag t b -> TagT tag u c -> TagT tag v d;
liftTagT3 f xt@(TagT r x) yt@(TagT s y) zt@(TagT t z) = TagT (r <> s <> t) (f xt yt zt);
