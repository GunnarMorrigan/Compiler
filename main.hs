{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Applicative
import Data.Char


-- ======================================== SPL Grammar ========================================

data VarDecl = VarDeclVar String Exp
             | VarDeclType SPLType String Exp

data FunDecl = FunDeclFun String Fargs FunType [VarDecl] [Stmt]

data FunType = P

data FTypes = Undef

data SPLType = TypeBasic BasicType
          | TypeTuple (SPLType, SPLType)
          | TypeArray [SPLType]
          deriving (Show, Eq)
          
data BasicType
  = BasicInt Integer
  | BasicBool Bool
  | BasicChar Char
  deriving (Show, Eq)

data Fargs = Hallo

data Stmt = Statement

data Exp = ExpId Id Field
         | ExpInt Integer
         | ExpChar Char
         | ExpBool Bool
         | BracketExp Exp
         | ExpOp2 Exp Op2 Exp
         | ExpOp1 Exp
         | ExpFunCall FunCall
         -- | ExpArray 
         -- | ExpTuple (Exp, Exp)

-- TODO: Types kloppen niet helemaal meer met beschrijving, zorg dat het in EXp komt te staan

data Op2 = Empty 
data Id = Doei 
data Field = Fjeld
data FunCall = CallFun



newtype Code = Code [(Char, Int, Int)]
  deriving (Show)

-- ======================================== Parser Error ========================================

data Error = Error Int Int String
  deriving (Show)

instance Alternative (Either Error) where
  empty = Left $ Error 0 0 ""
  Left _ <|> e2 = e2
  e1 <|> _ = e1

-- ======================================== Parser ========================================

newtype Parser x = Parser
  {run :: Code -> Either Error (x, Code)}

instance Functor Parser where
  fmap f (Parser p) =
    Parser $ \input -> do
      (out, input') <- p input
      Right (f out, input')

instance Applicative Parser where
  pure p = Parser $ \input -> Right (p, input)
  (Parser p1) <*> (Parser p2) =
    Parser $ \input -> do
      (f, input') <- p1 input
      (out, input'') <- p2 input'
      Right (f out, input'')

instance Alternative Parser where
  empty = Parser $ const empty
  (Parser p1) <|> (Parser p2) = Parser $ \input -> p1 input <|> p2 input


-- ======================================== Helper functions ========================================

stringToCode :: String -> Code
stringToCode x = Code <$> concat $ zipWith lineToCode (lines x) [1 ..]

lineToCode :: String -> Int -> [(Char, Int, Int)]
lineToCode s line = zip3 s (repeat line) [1 ..]

charP :: Char -> Parser Char
charP char = Parser f
  where
    f (Code x) =
      case x of
        (ch, line, col) : xs | ch == char -> Right (ch, Code xs)
        (ch, line, col) : xs -> Left $ Error line col ("Expect " ++ [char] ++ " but found " ++ [ch])
        _ -> Left $ Error 0 0 ("Unexpected EOF, expected: " ++ [char])


stringP :: String -> Parser String
stringP s = Parser f
    where
        f x =
            case run (traverse charP s) x of
                Left (Error line col error) -> Left $ Error line col ("Could not match with " ++ s)
                x -> x

spanP :: ((Char, Int, Int) -> Bool) -> Parser String
spanP f =
  Parser $ \(Code input) ->
  let (token, rest) = span f input
  in Right (map (\(a,b,c) -> a ) token, Code rest)

sepBy :: Parser a -> Parser b -> Parser [b]
sepBy sep elem = (:) <$> elem <*> many (sep *> elem) <|> pure []

ws :: Parser String
ws = spanP (\(a,b,c) -> isSpace a)

notEmpty :: Parser [a] -> Parser [a]
notEmpty (Parser p) = 
  Parser $ \input -> do
    (xs, input') <- p input
    if null xs
      then Left $ Error 0 0 "No input numbers found"
    else Right (xs, input')

charLiteral :: Parser Char
charLiteral = Parser f
  where
    f (Code (x : xs)) =
      case x of
        (ch, line, col) -> Right (ch, Code xs)

-- ======================================== BasicType ========================================

basicChar :: Parser BasicType
basicChar = BasicChar <$> (charP '\'' *> charLiteral <* charP '\'')

basicBool :: Parser BasicType
basicBool = (BasicBool True <$ stringP "true") <|>
            (BasicBool False <$ stringP "false")

-- TODO: Implement notNull
-- It works but not when there are no numbers the same was the case for the tutorial
basicInt :: Parser BasicType
basicInt = f <$> notEmpty (spanP (\(a,b,c) -> isDigit a))
  where f x = BasicInt(read x)

basicType :: Parser BasicType
basicType = basicChar <|> basicInt <|>  basicBool

-- ======================================== SPLType ========================================

-- This should become exp and BasicType should be implemented differently

typeTuple :: Parser SPLType
typeTuple = TypeTuple <$> (charP '(' *> ws *> elems <* ws <* charP ')')
  where elems = (\first _ second -> (first, second)) <$> splType <*> (ws *> charP ',' <* ws) <*> splType
    
--We assumed that array elements in SPL are seperated by a comma
typeArray :: Parser SPLType
typeArray = TypeArray <$> (charP '[' *> ws *> elems <* ws <* charP ']')
  where elems = sepBy (ws *> charP ',' <* ws ) splType

splType :: Parser SPLType
splType = typeTuple <|> typeArray <|> TypeBasic <$> basicType

-- ==========================================================================================

main :: IO ()
main = undefined
