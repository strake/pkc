{-# LANGUAGE TemplateHaskell #-}

module Lex where

import Control.Applicative;
import Control.Arrow;
import Control.Category.Unicode;
import Control.Monad;
import Control.Monad.Except;
import Control.Monad.State;
import Control.Monad.State.Lens as ML;
import Data.Char;
import Data.Lens.TH;
import Data.Token;
import Data.Eq.Unicode;
import Data.Foldable.Unicode;
import Data.Text.Pos;
import Text.Regex.Applicative;
import Util;

data LexerState = LexSt {
  _lexInput :: [Char],
  _lexPos :: TextPos
};

mkLens (dropWhile (== '_')) ''LexerState;

scan1M :: (Applicative m, MonadError e m, MonadState LexerState m) => e -> m Token;
scan1M e =
  ML.gets lexInput >>= \ case {
    [] -> return EOF;
    xs -> case findLongestPrefix (withMatched $ reSpace *> reLexeme <* reSpace) xs of {
      Nothing -> throwError e;
      Just ((t, ys), xs) -> t <$ (ML.puts lexInput xs *> ML.modify lexPos (flip (foldr textMov) ys));
    };
  };

reLexeme :: RE Char Token;
reLexeme =
  foldr1 (<|>)
  [LBrace   <$ sym '{', RBrace   <$ sym '}',
   LBracket <$ sym '[', RBracket <$ sym ']',
   LParenth <$ sym '(', RParenth <$ sym ')',
   SemiColon <$ sym ';', Comma <$ sym ',',
   reKeyWord, reTermName, reTypeName, reSymbol, reLInteger];

reSpace :: RE Char ();
reSpace = () <$ many (reComment <|> () <$ psym isSpace);

reComment :: RE Char ();
reComment = () <$ (sym '-' *> some (sym '-') *> (string "\n" <|> psym (/= '-') *> many (psym (≠ '\n'))));

reKeyWord :: RE Char Token;
reKeyWord = KeyWord <$>
  (foldr1 (<|>) ∘ fmap string)
  ["_", "with", "for", "return", "@", "*", ".", ":", "≔"];

reTermName :: RE Char Token;
reTermName = TermName <$> liftA2 (:) (psym (isLower <||> (== '_'))) (many (psym (isAlphaNum <||> (== '_'))));

reTypeName :: RE Char Token;
reTypeName = TypeName <$> liftA2 (:) (psym isUpper) (many (psym (isAlphaNum <||> (== '_'))));

reSymbol :: RE Char Token;
reSymbol = Symbol <$> some (psym ((isSymbol <||> isPunctuation <&&> (≠ '_')) <&&> (∉ "()[]{};,")));

reLInteger :: RE Char Token;
reLInteger = IntegerLiteral <$> reInteger;

reInteger :: RE Char Integer;
reInteger = reNumber 10 <|>
            (foldr1 (<|>) ∘ fmap (sym '0' *>))
            [psym (∈ "Bb") *> reNumber  2,
             psym (∈ "Oo") *> reNumber  8,
             psym (∈ "Dd") *> reNumber 10,
             psym (∈ "Xx") *> reNumber 16];

reNumber :: Int -> RE Char Integer;
reNumber n = foldl (\ m m' -> toInteger n*m + toInteger m') 0 <$> some (reNumeral n);

reNumeral :: Int -> RE Char Int;
reNumeral n | n <=  0 = empty
            | n <= 10 = (− fromEnum '0') ∘ fromEnum <$> psym (∈ take  n     ['0'..])
            | n <= 36 = (+ 10) ∘ (− fromEnum 'a') ∘ fromEnum <$> psym (∈ take (n-10) ['a'..]) <|>
                        (+ 10) ∘ (− fromEnum 'A') ∘ fromEnum <$> psym (∈ take (n-10) ['A'..]) <|>
                        reNumeral 10
            | otherwise = error ("Numeric radix " ++ show n ++ " too great")
            ;

(−) = (-);

textMov :: Char -> TextPos -> TextPos;
textMov '\r' (TextPos (m, _)) = TextPos (m,   0);
textMov '\n' (TextPos (m, _)) = TextPos (m+1, 0);
textMov '\b' (TextPos (m, n)) = TextPos (m, n-1);
textMov   _  (TextPos (m, n)) = TextPos (m, n+1);
