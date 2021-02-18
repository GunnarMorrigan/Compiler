{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Parser where 

import Control.Applicative
import Data.Char
import Lexer
import AST
import Data.Typeable


import Control.Monad
import Data.Functor; import Data.Function
import Data.List

-- ======================================== Parser Error ========================================

-- data Error = Error Int Int String
--   deriving (Show)

-- instance Alternative (Either Error) where
--   empty = Left $ Error 0 0 ""
--   Left _ <|> e2 = e2
--   e1 <|> _ = e1

newtype Parser s a = Parser {run :: [s] -> Either Error (a, [s])}

instance Functor (Parser s) where
  fmap f (Parser p) =
    Parser $ \input -> do
      (out, input') <- p input
      Right (f out, input')

instance Applicative (Parser s) where
  pure p = Parser $ \input -> Right (p, input)
  (Parser p1) <*> (Parser p2) =
    Parser $ \input -> do
      (f, input') <- p1 input
      (out, input'') <- p2 input'
      Right (f out, input'')

instance Alternative (Parser s) where
  empty = Parser $ const empty
  (Parser p1) <|> (Parser p2) = Parser $ \input -> p1 input <|> p2 input

-- satisfy :: ((Token, Int, Int) -> Bool) -> (Token -> a ) -> (Token -> String) -> Parser s a
-- satisfy f g message = Parser $ \case 
--        (s, line, col):rest | f (s, line, col) -> Right (g s, rest)
--        (x, line, col):xs -> Left $ Error line col (message x)

satisfy :: ((Token, Int, Int) -> Bool) -> (Token -> a) -> Parser (Token, Int, Int) a
satisfy f g = Parser $ \case 
       (s, line, col):rest | f (s, line, col) -> Right (g s, rest)
       (x, line, col):xs -> Left $ Error line col ""
       _ -> Left $ Error 0 0 ""

pChainl :: Parser s (a -> a -> a) -> Parser s a -> Parser s a
pChainl op p = foldl (&) <$> p <*> many (flip <$> op <*> p)

pToken :: Token -> Parser (Token, Int, Int) Token
pToken t = Parser $ \case 
                     (x, line, col):xs | x == t -> Right (x,xs)
                     (x, line, col):xs -> Left $ Error line col ("Expected: "++show t++" but found" ++ show x)
                     
-- ===================== Expressions ============================


-- ExpOp2 Exp Op2 Exp
-- ExpFunCall FunCall

expInt :: Parser (Token, Int, Int) Exp
expInt = ExpInt <$> Parser (\case
              (IntToken c,line,col):xs -> Right (c,xs)
              (x, line, col):xs -> Left $ Error line col ("Expected Integer but got token: " ++ show x))

expChar :: Parser (Token, Int, Int) Exp
expChar = ExpChar <$> Parser (\case
       (CharToken c,line,col):xs -> Right (c,xs)
       (x, line, col):xs -> Left $ Error line col ("Expected Char but got token: " ++ show x))

expBool :: Parser (Token, Int, Int) Exp
expBool = ExpBool <$> Parser (\case
       (BoolToken b, line, col):xs -> Right (b,xs)
       (x, line, col):xs -> Left $ Error line col ("Expected Bool but got token: " ++ show x))

-- Maybe Not usable?
-- expBracket :: Parser (Token, Int, Int) Exp
-- expBracket = pToken BrackOpenToken  *> expParser <* pToken BrackCloseToken 

expOp1 :: Parser (Token, Int, Int) Exp
expOp1 = ExpOp1 <$> (Neg <$ pToken MinToken <|> Not <$ pToken NotToken) <*> expParser

expEmptyList :: Parser (Token, Int, Int) Exp 
expEmptyList = ExpEmptyList <$ pToken EmptyListToken 

expList :: Parser (Token, Int, Int) Exp 
expList = ExpList <$> (pToken SquareBrackOpenToken *> expList <* pToken SquareBrackCloseToken)
       where expList = many expParser <* pToken CommaToken
       
expTuple :: Parser (Token, Int, Int) Exp 
expTuple = ExpTuple <$> tuple
       where tuple = (,) <$> expParser <*> expParser

basicExpParser :: Parser (Token, Int, Int) Exp 
basicExpParser = expTuple <|> expList <|> expEmptyList <|> expOp1 <|> expBool <|> expChar

expParser :: Parser (Token, Int, Int) Exp 
expParser = undefined 

-- pExpr  = pChainl (op '+' <|> op '-') pFact
-- pFact  = pChainl (op '*' <|> op '/') pPow
-- pPow   =   BinOp <$> pBasic <*> symbol '^' <*> pExpr
--        <|> pBasic
-- pBasic =   parens pExpr
--        <|> Val . read <$> some pDigit
--        <|> Id <$> some pAlpha

runX :: [Char] -> p -> Either Error (Exp, [(Token, Int, Int)])
runX x y = runTokenise x >>= run expChar
main = runTokenise "\'x\'" >>= run expChar