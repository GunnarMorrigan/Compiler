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

data SPLType 
  = TypeBasic BasicType
  | TupleType (SPLType, SPLType)
  | ArrayType SPLType
  deriving (Show, Eq)
          
data BasicType
  = BasicInt
  | BasicBool
  | BasicChar
  deriving (Show, Eq)

data Fargs = Hallo

data Stmt = IfStmt (Exp, [Stmt]) [(Exp, [Stmt])]
            | WhileStmt Exp Stmt

data Exp 
  = ExpId String Field
  | ExpInt Integer
  | ExpChar Char
  | ExpBool Bool
  | ExpBracket Exp
  | ExpOp2 Exp Op2 Exp
  | ExpOp1 Op1 Exp
  | ExpFunCall FunCall
  | ExpArray [Exp]
  | ExpTuple (Exp, Exp)
  deriving (Show, Eq)

         -- | ExpArray 
         -- | ExpTuple (Exp, Exp)
        
-- TODO: Types kloppen niet helemaal meer met beschrijving, zorg dat het in EXp komt te staan
data Op1 = Not
         | Neg
        deriving (Show, Eq)
        
data Op2 = Plus|Min|Mult|Div|Mod|Eq|Le|Ge|Leq|Geq|Neq|And|Or|Con
         deriving (Show, Eq)

-- data Id = Doei
--         deriving (Show, Eq)

data Field = Fjeld
            deriving (Show, Eq)

data FunCall = CallFun
        deriving (Show, Eq)


newtype Code = Code [(Char, Int, Int)]
  deriving (Show, Eq)

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


-- idLiteral :: Parser String
-- idLiteral = Parser f
--   where 
--     f (Code (x:xs)) = 
--       case x of (ch, line, col) -> Left (ch, Code xs)

-- idLiteral :: Parser String
-- idLiteral = \input -> 
--   case run (spanP (\(c,line,col) -> isAlpha c)) input of
--     Right (x, y) -> Error 0 0 "Can't match with an ID"
    -- Right ([], ((Code (c, line, col)):ys)) -> Error line col "Can't match with an ID"


    -- Right ((x:xs), code) -> 
    --   let Right (s, code') = run (spanP (\(c,line,col) -> isAlphaNum c || c == '_')) code
    --   in Right ((x:xs)++s, code')
  
-- let Right s (Code x:xs) = run (spanP (\(c,line,col) -> isAlpha c) input 
-- in 
-- <*> spanP (\(c,line,col) -> isAlphaNum c || c == '_')
-- idLiteral = ((++) . concat <$> some(spanP (\(c,line,col) -> isAlpha c))) <*> (concat <$> many(spanP (\(c,line,col) -> isAlphaNum c)))

-- ======================================== SPLType ========================================

tupleType :: Parser SPLType
tupleType = TupleType <$> (charP '(' *> ws *> elems <* ws <* charP ')')
  where elems = (\first _ second -> (first, second)) <$> splType <*> (ws *> charP ',' <* ws) <*> splType

arrayType :: Parser SPLType
arrayType = ArrayType <$> (charP '[' *> ws *> splType <* ws <* charP ']')

splType :: Parser SPLType
splType =  arrayType <|> tupleType <|> TypeBasic <$> basicType

-- ======================================== BasicType ========================================

basicInt :: Parser BasicType
basicInt = BasicInt <$ stringP "Int"

basicBool :: Parser BasicType
basicBool = BasicBool <$ stringP "Bool"

basicChar :: Parser BasicType
basicChar = BasicChar <$ stringP "Char"

basicType :: Parser BasicType
basicType = basicInt <|> basicBool <|> basicChar

-- ======================================== Exp ========================================

expChar :: Parser Exp
expChar = ExpChar <$> (charP '\'' *> charLiteral <* charP '\'')

expBool :: Parser Exp
expBool = (ExpBool True <$ stringP "True") <|>
            (ExpBool False <$ stringP "False")

-- TODO: Implement notNull
-- It works but not when there are no numbers the same was the case for the tutorial
expInt :: Parser Exp
expInt = f <$> notEmpty (spanP (\(a,b,c) -> isDigit a))
  where f x = ExpInt(read x)

expTuple :: Parser Exp
expTuple = ExpTuple <$> (charP '(' *> ws *> elems <* ws <* charP ')')
  where elems = (\first _ second -> (first, second)) <$> parserExp <*> (ws *> charP ',' <* ws) <*> parserExp

--We assumed that array elements in SPL are seperated by a comma
expArray :: Parser Exp
expArray = ExpArray <$> (charP '[' *> ws *> elems <* ws <* charP ']')
  where elems = sepBy (ws *> charP ',' <* ws ) parserExp

expOp1 :: Parser Exp
expOp1 = ExpOp1 <$> op1 <*> parserExp

expOp2 :: Parser Exp
expOp2 = ExpOp2 <$> parserExp <*> op2 <*> parserExp

expBracket :: Parser Exp
expBracket = ExpBracket <$> (charP '(' *> ws *> parserExp <* ws <* charP ')')
 
parserExp :: Parser Exp
parserExp = expChar <|> expInt <|> expBool <|> expArray <|> expTuple <|> expOp1 <|> expOp2

-- ======================================== Stmt ============================================
--data Stmt = IfStmt (Exp, Stmt) [(Exp, Stmt)]
            -- | WhileStmt Exp Stmt

-- ifStmt :: Parser Stmt
-- ifStmt = IfStmt <$> (stringP "if" *> ws *> charP '(' *> ws *> parserExp <* ws <* charP ')' <*> 
--                     charP '{' *> ws *> stmts <* ws <* charP '}') <*> []
--                     where stmts = sepBy (ws *> charP ';' <* ws) stmt

-- stmt :: Parser Stmt
-- stmt = ifStmt

-- ======================================== Op ==============================================
op1 :: Parser Op1
op1 = (Not <$ charP '!') <|> (Neg <$ charP '-')

op2 :: Parser Op2
op2 = (Plus <$ charP '+') <|>
      (Min <$ charP '-') <|>
      (Mult <$ charP '*') <|>
      (Div <$ charP '/') <|>
      (Mod <$ charP '%') <|>
      (Eq <$ stringP "==") <|>
      (Le <$ charP '<') <|>
      (Ge <$ charP '>') <|>
      (Leq <$ stringP "<=") <|>
      (Geq <$ stringP ">=") <|>
      (Neq <$ stringP "!=") <|>
      (And <$ stringP "&&") <|>
      (Or <$ stringP "||") <|>
      (Con <$ charP ':')
-- ==========================================================================================
  


main :: IO ()
main = undefined
