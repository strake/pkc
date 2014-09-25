module Lex where

import Control.Applicative;
import Control.Arrow;
import Control.Category.Unicode;
import Data.Char;
import Data.Token;
import Data.Eq.Unicode;
import Data.Foldable.Unicode;
import Text.Regex.Applicative;
import Util;

scan :: [Char] -> [Token];
scan [] = [];
scan xs = maybe (error "scan failure") (id *** scan >>> uncurry (:)) $ findLongestPrefix (reSpace *> reLexeme <* reSpace) xs;

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
  ["with", "@", "*", ".", ":", "≔"];

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
