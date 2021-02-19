{-# LANGUAGE FlexibleInstances #-}
module Lexer where

import Control.Applicative
import Data.Char

data Error = Error Int Int String

instance Eq Error where
  (==) (Error line col m) (Error line' col' m') =  line == line' && col == col'

instance Ord Error where
  (Error line col m) `compare` (Error line' col' m') = if line == line' then compare col col' else compare line line'

instance Show Error where
       show (Error line col message) = message ++ ", on line: " ++show line ++ " and character: " ++ show col 

instance Alternative (Either Error) where
  empty = Left $ Error 0 0 ""
  Left x <|> Left y = Left $ max x y
  Left _ <|> e2 = e2
  e1 <|> _ = e1


newtype Code = Code [(Char, Int, Int)]
  deriving (Show, Eq)

data Token
  = VarToken| IntToken Integer| BoolToken Bool| CharToken Char
  | TypeIntToken| TypeBoolToken| TypeCharToken
  | SemiColToken| CommaToken| IsToken
  | FunTypeToken| ArrowToken| VoidToken| ReturnToken
  | EmptyListToken| BrackOToken| BrackCToken| CBrackOToken| CBrackCToken| SBrackOToken| SBrackCToken
  | HdToken| TlToken| FstToken| SndToken| IsEmptyToken
  | PlusToken| MinToken| MultToken| DivToken| ModToken 
  | EqToken| LeToken | GeToken | LeqToken | GeqToken| NeqToken| AndToken| OrToken| ConstToken| NotToken
  | IdToken String
  | IfToken| ElseToken| WhileToken
  deriving (Eq)
instance Show Token where
  show VarToken = "var"
  show (IntToken x) = show x
  show (BoolToken x) = show x
  show (CharToken x) = show x
  show TypeIntToken = "Int"
  show TypeBoolToken = "Bool"
  show TypeCharToken = "Char"
  show SemiColToken = ";"
  show CommaToken = ","
  show IsToken = "="
  show FunTypeToken = "::"
  show ArrowToken = "->"
  show VoidToken = "Void"
  show ReturnToken = "return"
  show EmptyListToken = "[]"
  show BrackOToken = "("
  show BrackCToken = ")"
  show CBrackCToken = "}"
  show CBrackOToken = "{"
  show SBrackCToken = "]"
  show SBrackOToken = "["
  show HdToken = ".hd"
  show TlToken = ".tl"
  show FstToken = ".fst"
  show SndToken = ".snd"
  show IsEmptyToken = ".isEmpty"
  show PlusToken = "+"
  show MinToken = "-"
  show MultToken = "*"
  show DivToken = "/"
  show ModToken = "%"
  show EqToken = "=="
  show LeToken = "<"
  show GeToken = ">"
  show LeqToken = "<="
  show GeqToken = ">="
  show NeqToken = "!="
  show AndToken = "&&"
  show OrToken = "||"
  show ConstToken = ":"
  show NotToken = "!"
  show (IdToken x) = "id["++x++"]"
  show IfToken = "if"
  show ElseToken = "else"
  show WhileToken = "while"

stringToCode x = Code <$> concat $ zipWith (\s line -> zip3 s (repeat line) [1 ..]) (lines x) [1 ..]

alphaCheck :: [Char] -> Bool
alphaCheck xs = null xs || not (isAlphaNum (head xs))

runTokenise :: [Char] -> Either Error [(Token, Int, Int)]
runTokenise x = tokenise x 0 0

tokenise :: [Char] -> Int -> Int -> Either Error [(Token, Int, Int)]
tokenise ('/' : '*' : xs) line col = gulp xs line col
  where
    gulp ('*' : '/' : rest) line col = tokenise rest line (col + 2)
    gulp (c : rest) line col = gulp rest line (col + 1)
    gulp [] line col = Right []
tokenise ('/' : '/' : xs) line col = tokenise (dropWhile (/= '\n') xs) (line + 1) 0
tokenise (' ' : xs) line col = tokenise xs line (col + 1)
tokenise ('[' : ']' : xs) line col = ((EmptyListToken, line, col) :) <$> tokenise xs line (col + 6)
tokenise ('\t' : xs) line col = tokenise xs line (col + 1)
tokenise ('\n' : xs) line col = tokenise xs (line + 1) 0
tokenise ('(' : xs) line col = ((BrackOToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise (')' : xs) line col = ((BrackCToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise ('{' : xs) line col = ((CBrackOToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise ('}' : xs) line col = ((CBrackCToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise ('[' : xs) line col = ((SBrackOToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise (']' : xs) line col = ((SBrackCToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise (':' : ':' : xs) line col = ((FunTypeToken, line, col) :) <$> tokenise xs line (col + 2)
tokenise ('-' : '>' : xs) line col = ((ArrowToken, line, col) :) <$> tokenise xs line (col + 2)
tokenise (';' : xs) line col = ((SemiColToken, line, col) :) <$> tokenise xs line (col + 1)

tokenise ('v': 'a': 'r':xs) line col | alphaCheck xs = ((VarToken, line, col) :) <$> tokenise xs line (col + 3)
tokenise ('r' : 'e' : 't' : 'u' : 'r' : 'n' : xs) line col | alphaCheck xs = ((ReturnToken, line, col) :) <$> tokenise xs line (col + 6)
tokenise ('V' : 'o' : 'i' : 'd' : xs) line col | alphaCheck xs = ((VoidToken, line, col) :) <$> tokenise xs line (col + 4)
tokenise ('T' : 'r' : 'u' : 'e' : xs) line col | alphaCheck xs = ((BoolToken True, line, col) :) <$> tokenise xs line (col + 4)
tokenise ('F' : 'a' : 'l' : 's' : 'e' : xs) line col | alphaCheck xs = ((BoolToken False, line, col) :) <$> tokenise xs line (col + 4)
tokenise ('I' : 'n' : 't' : xs) line col | alphaCheck xs = ((TypeIntToken, line, col) :) <$> tokenise xs line (col + 3)
tokenise ('B' : 'o' : 'o' : 'l' : xs) line col | alphaCheck xs = ((TypeBoolToken, line, col) :) <$> tokenise xs line (col + 4)
tokenise ('C' : 'h' : 'a' : 'r' : xs) line col | alphaCheck xs = ((TypeCharToken, line, col) :) <$> tokenise xs line (col + 4)
tokenise ('i' : 'f' : xs) line col | alphaCheck xs = ((IfToken, line, col) :) <$> tokenise xs line (col + 2)
tokenise ('e' : 'l' : 's' : 'e' : xs) line col | alphaCheck xs = ((ElseToken, line, col) :) <$> tokenise xs line (col + 4)
tokenise ('w' : 'h' : 'i' : 'l' : 'e' : xs) line col | alphaCheck xs = ((WhileToken, line, col) :) <$> tokenise xs line (col + 5)
tokenise ('.' : 'h' : 'd' : xs) line col | alphaCheck xs = ((HdToken, line, col) :) <$> tokenise xs line (col + 3)
tokenise ('.' : 't' : 'l' : xs) line col | alphaCheck xs = ((TlToken, line, col) :) <$> tokenise xs line (col + 3)
tokenise ('.' : 'f' : 's' : 't' : xs) line col | alphaCheck xs = ((FstToken, line, col) :) <$> tokenise xs line (col + 4)
tokenise ('.' : 's' : 'n' : 'd' : xs) line col | alphaCheck xs = ((SndToken, line, col) :) <$> tokenise xs line (col + 4)
tokenise ('.' : 'i' : 's' : 'E' : 'm' : 'p' : 't' : 'y' : xs) line col | alphaCheck xs = ((IsEmptyToken, line, col) :) <$> tokenise xs line (col + 8)
-- tokenise ('.':xs) line col = ((DotToken,line,col):) <$> tokenise xs line (col + 1)

tokenise ('=' : '=' : xs) line col = ((EqToken, line, col) :) <$> tokenise xs line (col + 2)
tokenise ('<' : '=' : xs) line col = ((LeqToken, line, col) :) <$> tokenise xs line (col + 2)
tokenise ('>' : '=' : xs) line col = ((GeqToken, line, col) :) <$> tokenise xs line (col + 2)
tokenise ('!' : '=' : xs) line col = ((NotToken, line, col) :) <$> tokenise xs line (col + 2)
tokenise ('&' : '&' : xs) line col = ((AndToken, line, col) :) <$> tokenise xs line (col + 2)
tokenise ('|' : '|' : xs) line col = ((OrToken, line, col) :) <$> tokenise xs line (col + 2)
tokenise ('=' : xs) line col = ((IsToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise ('+' : xs) line col = ((PlusToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise ('-' : xs) line col = ((MinToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise ('*' : xs) line col = ((MultToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise ('/' : xs) line col = ((DivToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise ('%' : xs) line col = ((ModToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise ('<' : xs) line col = ((LeToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise ('>' : xs) line col = ((GeToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise (':' : xs) line col = ((ConstToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise ('!' : xs) line col = ((NotToken, line, col) :) <$> tokenise xs line (col + 1)
tokenise (',' : xs) line col = ((CommaToken,line,col):) <$> tokenise xs line (col + 1)
tokenise ('\'' : x : '\'' : xs) line col = ((CharToken x, line, col) :) <$> tokenise xs line (col + 3)
tokenise (c : xs) line col
  | isSpace c = tokenise xs line col
  | isDigit c = spanToken isDigit line col (IntToken . read) (c : xs)
  | isAlpha c = spanToken (\c -> isAlphaNum c || c == '_') line col IdToken (c : xs)
  | otherwise = Left $ Error line col ("Unrecognized character: " ++ show c)
tokenise [] line col = Right []

spanToken :: (Char -> Bool) -> Int -> Int -> ([Char] -> Token) -> [Char] -> Either Error [(Token, Int, Int)]
spanToken p line col t = (\(ds, rest) -> ((t ds, line, col) :) <$> tokenise rest line (col + length ds)) . span p
