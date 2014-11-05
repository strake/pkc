Main: Data/PrimOp.hs Util/LLVM/Type.hs Util/LLVM/Pretty.hs Data/STRef/Lifted.hs Util/Lens/Monadic.hs Data/Syntax.hs Data/CodeGenTypes.hs CodeGen/Common.hs CodeGen.hs Destruct.hs Lex.hs Parse.hs Main.hs
	ghc --make -j -XUnicodeSyntax -XLambdaCase -XTypeOperators -XViewPatterns -XNoMonomorphismRestriction -XRankNTypes -XScopedTypeVariables -XGADTs -XFlexibleContexts -XFlexibleInstances -XConstraintKinds -XImpredicativeTypes -XDeriveFunctor Main

Parse.hs: Parse.g
	frown -Occompact Parse.g

clean:V:
	find . | 9 grep '(\.(dyn_)?(hi|o)|^(./)?Parse.hs[0-9]*)$' | xargs rm -f
	rm -f Main
