module Parse where

import Control.Applicative;
import Data.LTree;
import Data.Map (Map);
import qualified Data.Map as Map;
import Data.Maybe;
import Data.PrimOp;
import Data.Syntax;
import Data.Token;
import Data.Linkage as L;

%{

Terminal	= LParenth as '(' | RParenth as ')'
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

top		{ [(Decl [Char], Linkage, Mutability, Type [Char], Maybe (Expr [Char]))] };
top		{ ds }							: sepEndBy topDecl ';' { ds };

topDecl		{ (Decl [Char], Linkage, Mutability, Type [Char], Maybe (Expr [Char])) };
topDecl		{ (VarDecl v, L.External, True,  t, Nothing) }		: termName { v }, ":", type { t };
topDecl		{ (VarDecl v, L.External, True,  t, Just x) }		: termName { v }, ":", type { t }, "≔", expr { x };
topDecl		{ (FuncDecl v parm, L.External, False, t, Nothing) }	: termName { v }, parm { parm }, ":", type { t };
topDecl		{ (FuncDecl v parm, L.External, False, t, Just x) }	: termName { v }, parm { parm }, ":", type { t }, "≔", expr { x };

parm		{ LTree [] (Maybe [Char], Type [Char]) };
parm		{ stlist id Stem parm }					: '(', sepBy parm ',' { parm }, ')';
parm		{ Leaf (Just v, t) }					: termName { v }, ":", type { t };
parm		{ Leaf (Nothing, t) }					: "_", ":", type { t };

expr		{ Expr [Char] };
expr		{ x }							: expr7 { x };

expr0		{ Expr [Char] };
expr0		{ stlist id Tuple xs }					: '(', sepBy expr ',' { xs }, ')';
expr0		{ foldr Then (fromMaybe (Tuple []) m_x) (x:xs) }	: '(', expr { x }, ';', sepEndBy expr ';' { xs }, opt expr { m_x }, ')';
expr0		{ Var v }						: termName { v };
expr0		{ Literal (LInteger n) }				: IntegerLiteral { n };

expr1		{ Expr [Char] };
expr1		{ x }							: expr0 { x };
expr1		{ Member x sel }					: expr1 { x }, ".", selector { sel };

selector	{ Either (LTree [] Int) (LTree [] [Char]) };
selector	{ Left  kt }						: deepNest "<integer>" '(' ',' ')' { fmap fromIntegral -> kt };
selector	{ Right vt }						: deepNest termName '(' ',' ')' { vt };

expr2a		{ Expr [Char] };
expr2a		{ x }							: expr1 { x };
expr2a		{ Call f x }						: expr2a { f }, expr1 { x };

expr2b		{ Expr [Char] };
expr2b		{ Return m_x }						: "return", opt expr1 { m_x };

expr2		{ Expr [Char] };
expr2		{ x }							: expr2a { x };
expr2		{ x }							: expr2b { x };

expr3		{ Expr [Char] };
expr3		{ x }							: expr2 { x };
expr3		{ Follow x }						: "*", expr3 { x };
expr3		{ PrimOp PrimNeg [x] }					: Symbol "¬", expr3 { x };

expr4		{ Expr [Char] };
expr4		{ x }							: expr3 { x };
expr4		{ Conj x y }						: expr4 { x }, Symbol "&&", expr4 { y };
expr4		{ Disj x y }						: expr4 { x }, Symbol "?!", expr4 { y };
expr4		{ PrimOp PrimEq [x, y] }				: expr4 { x }, Symbol "=", expr4 { y };
expr4		{ PrimOp PrimNEq [x, y] }				: expr4 { x }, Symbol "≠", expr4 { y };
expr4		{ PrimOp PrimGEq [x, y] }				: expr4 { x }, Symbol "≥", expr4 { y };
expr4		{ PrimOp PrimLEq [x, y] }				: expr4 { x }, Symbol "≤", expr4 { y };
expr4		{ PrimOp PrimGÞ [x, y] }				: expr4 { x }, Symbol ">", expr4 { y };
expr4		{ PrimOp PrimLÞ [x, y] }				: expr4 { x }, Symbol "<", expr4 { y };
expr4		{ PrimOp PrimAnd [x, y] }				: expr4 { x }, Symbol "∧", expr4 { y };
expr4		{ PrimOp PrimOr  [x, y] }				: expr4 { x }, Symbol "∨", expr4 { y };
expr4		{ PrimOp PrimXor [x, y] }				: expr4 { x }, Symbol "⊻", expr4 { y };
expr4		{ PrimOp PrimXor
		  [PrimOp PrimAnd [x, y],
		   Literal (LInteger (negate 1))] }			: expr4 { x }, Symbol "⊼", expr4 { y };
expr4		{ PrimOp PrimXor
		  [PrimOp PrimOr  [x, y],
		   Literal (LInteger (negate 1))] }			: expr4 { x }, Symbol "⊽", expr4 { y };
expr4		{ PrimOp PrimRotL [x, y] }				: expr4 { x }, Symbol "<<<", expr4 { y };
expr4		{ PrimOp PrimRotR [x, y] }				: expr4 { x }, Symbol ">>>", expr4 { y };
expr4		{ PrimOp PrimShiftL [x, y] }				: expr4 { x }, Symbol "<<", expr4 { y };
expr4		{ PrimOp PrimShiftR [x, y] }				: expr4 { x }, Symbol ">>", expr4 { y };
expr4		{ PrimOp PrimAdd [x, y] }				: expr4 { x }, Symbol "+", expr4 { y };
expr4		{ PrimOp PrimSub [x, y] }				: expr4 { x }, Symbol "-", expr4 { y };
expr4		{ PrimOp PrimMul [x, y] }				: expr4 { x }, Symbol "×", expr4 { y };
expr4		{ PrimOp PrimDiv [x, y] }				: expr4 { x }, Symbol "/", expr4 { y };

expr5		{ Expr [Char] };
expr5		{ x }							: expr4 { x };
expr5		{ If p x y }						: expr5 { p }, Symbol "?", expr5 { x }, Symbol "!", expr5 { y };

expr6		{ Expr [Char] };
expr6		{ x }							: expr5 { x };
expr6		{ Cast t x }						: expr6 { x }, ":", type { t };

expr7		{ Expr [Char] };
expr7		{ x }							: expr6 { x };
expr7		{ With (Map.fromList ds) x }				: KeyWord "with", '(', sepMayEndBy localDecl ',' { ds }, ')', expr7 { x };
expr7		{ y := let {
		         lookupBinOp :: [Char] -> Expr [Char] -> Expr [Char] -> Expr [Char];
		         lookupBinOp "" x y = y;
		         lookupBinOp "∧" x y = PrimOp PrimAnd [x, y];
		         lookupBinOp "∨" x y = PrimOp PrimOr  [x, y];
		         lookupBinOp "⊻" x y = PrimOp PrimXor [x, y];
		         lookupBinOp "⊼" x y =
		           PrimOp PrimXor
		           [PrimOp PrimAnd [x, y],
		            Literal (LInteger (negate 1))];
		         lookupBinOp "⊽" x y =
		           PrimOp PrimXor
		           [PrimOp PrimOr  [x, y],
		            Literal (LInteger (negate 1))];
		         lookupBinOp "<<" x y = PrimOp PrimShiftL [x, y];
		         lookupBinOp ">>" x y = PrimOp PrimShiftR [x, y];
		         lookupBinOp "<<<" x y = PrimOp PrimRotL [x, y];
		         lookupBinOp ">>>" x y = PrimOp PrimRotR [x, y];
		         lookupBinOp "+" x y = PrimOp PrimAdd [x, y];
		         lookupBinOp "-" x y = PrimOp PrimSub [x, y];
		         lookupBinOp "×" x y = PrimOp PrimMul [x, y];
		         lookupBinOp "/" x y = PrimOp PrimDiv [x, y];
		       } in lookupBinOp opv y x }			: expr6 { y }, assignOp { opv }, expr7 { x };
expr7		{ Loop p x y }						: "for", expr1 { p }, expr1 { x }, expr { y };

localDecl	{ ([Char], Type [Char]) };
localDecl	{ (v, t) }						: termName { v }, ":", type { t };

atype		{ Type [Char] };
atype		{ NamedType v }						: TypeName { v };
atype		{ stlist id TupleType ts }				: '(', sepBy type ',' { ts }, ')';
atype		{ TypeInteger n }					: "<integer>" { n };

ptype		{ Type [Char] };
ptype		{ t }							: atype { t };
ptype		{ Typlication s t }					: ptype { s }, atype { t };

qtype		{ Type [Char] };
qtype		{ t }							: ptype { t };
qtype		{ PtrType t }						: qtype { t }, "*";

type		{ Type [Char] };
type		{ t }							: qtype { t };
type		{ FuncType t s }					: type { t }, Symbol "->", qtype { s };

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

}%

frown ts = error ("parse failure: " ++ show ts);

stlist :: (a -> b) -> ([a] -> b) -> [a] -> b;
stlist f g [x] = f x;
stlist f g  xs = g xs;
