module Data.Token where

data Token = EOF
           | TermName [Char]
           | TypeName [Char]
           | Symbol [Char]
           | KeyWord [Char]
           | IntegerLiteral Integer
           | LBrace   | RBrace
           | LParenth | RParenth
           | LBracket | RBracket
           | SemiColon | Comma
  deriving (Eq, Show);
