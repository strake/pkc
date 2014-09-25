module Data.Token where

data Token = TermName [Char]
           | TypeName [Char]
           | Symbol [Char]
           | KeyWord [Char]
           | IntegerLiteral Integer
           | LBrace   | RBrace
           | LParenth | RParenth
           | LBracket | RBracket
           | SemiColon | Comma
  deriving (Eq, Show);
