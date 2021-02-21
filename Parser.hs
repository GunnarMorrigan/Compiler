{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Parser where 

import Control.Applicative
import Data.Char
import Lexer
import AST
import Data.Typeable
import Prelude
import Debug.Trace
import System.Exit
import System.Directory

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
  fmap f (Parser p) = Parser $ \input -> do
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

instance Monad (Parser s) where
    ma >>= a2mb = Parser $ \input -> do
              (a,b) <- run ma input
              (x,y) <- run (a2mb a) b
              Right(x, b)

-- infixr 4 <<|>
-- (<<|>) :: Parser s r -> Parser s r -> Parser s r
-- x <<|> y = Parser $ \input -> case input of
--     Left _  -> run y input
--     res -> res


-- infixr 4 <<|>
-- (<<|>) :: Parser s r -> Parser s r -> Parser s r
-- x <<|> y = Parser $ \input -> case input of
--     Left _  -> run y input
--     res -> res


--   (Parser p1) <|> (Parser p2) = Parser $ \input -> case  p1 input of
--          Right(a, xs) -> Right(a,xs)
--          Left (Error line col message) -> p2 input

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
pChainl x p = foldl (&) <$> p <*> many (flip <$> x <*> p)

op :: Parser (Token, Int, Int) Op2 -> Parser (Token, Int, Int) (Exp -> Exp -> Exp)
op p = flip ExpOp2 <$> p

pToken :: Token -> Parser (Token, Int, Int) Token
pToken t = Parser $ \case 
                     (x, line, col):xs | x == t -> Right (x,xs)
                     (x, line, col):xs -> Left $ Error line col ("Expected: "++show t++" but found: " ++ show x)
                     _ -> Left $ Error 0 0 "Unexpected token"

-- ===================== VarDecl ============================
varDecl :: Parser (Token, Int, Int) VarDecl 
varDecl = (VarDeclType <$> splType <*> idP <*> varAss) <|>
          (VarDeclVar <$> (pToken VarToken *> idP) <*> varAss)
          where varAss = pToken IsToken *>expParser <* pToken SemiColToken

-- ===================== FunDecl ============================ 
funDecl :: Parser (Token, Int, Int) FunDecl
funDecl = FunDecl <$> idP <*> (pToken BrackOToken *> many idP <* pToken BrackCToken) <*>
                     (pToken FunTypeToken *> funType) <*>
                     (pToken CBrackOToken*> many varDecl) <*>
                     some stmt <* pToken CBrackCToken

-- ===================== Types ============================

-- ===== FunType =====
funType :: Parser (Token, Int, Int) FunType 
funType = FunType <$> many splType <*> (pToken ArrowToken *> retType)
-- ===== RetType =====
retType :: Parser (Token, Int, Int) RetType
retType =  RetSplType <$> splType <|> Void <$ pToken VoidToken

-- ===== Type =====
splType :: Parser (Token, Int, Int) SPLType 
splType = (TypeBasic <$> basicType) <|> tupleType <|> arrayType

tupleType :: Parser (Token, Int, Int) SPLType 
tupleType = TupleType <$> ( pToken BrackOToken *> ((,) <$> splType <* pToken CommaToken  <*> 
                            splType) <* pToken BrackCToken)

arrayType :: Parser (Token, Int, Int) SPLType
arrayType = ArrayType <$> (pToken SBrackOToken *> splType <* pToken SBrackCToken)

-- ===== BasicType =====
basicInt :: Parser (Token, Int, Int) BasicType
basicInt = BasicInt <$ pToken TypeIntToken

basicBool :: Parser (Token, Int, Int) BasicType
basicBool = BasicBool <$ pToken TypeBoolToken

basicChar :: Parser (Token, Int, Int) BasicType
basicChar = BasicChar <$ pToken TypeBoolToken

basicType :: Parser (Token, Int, Int) BasicType
basicType = basicInt <|> basicBool <|> basicChar 

-- ===================== Statements ============================
-- StmtIf Exp [Stmt] Maybe [Stmt]
stmtIf :: Parser (Token, Int, Int) Stmt
stmtIf = StmtIf <$> 
       (pToken IfToken *> pToken BrackOToken *> expParser <* pToken BrackCToken) <*>
       (pToken CBrackOToken *> many stmt <* pToken CBrackCToken) <*> 
       stmtElse

stmtElse :: Parser (Token, Int, Int) (Maybe [Stmt])
stmtElse = Parser $ \case
       (ElseToken,line,col):xs -> do
              (ys,rest) <- run (pToken CBrackOToken *> many stmt <* pToken CBrackCToken) xs
              Right (Just ys, rest)
       x -> Right (Nothing,x)

stmtWhile :: Parser (Token, Int, Int) Stmt
stmtWhile = StmtWhile <$> 
       (pToken WhileToken *> pToken BrackOToken *> expParser <* pToken BrackCToken) <*>
       (pToken CBrackOToken *> ((:) <$> stmt <*> many ( pToken SemiColToken  *> stmt)) <* pToken CBrackCToken) 

stmtDeclareVar :: Parser (Token, Int, Int) Stmt
stmtDeclareVar = StmtDeclareVar <$> idP <*> (fieldP <* pToken IsToken)  <*> (expParser <* pToken SemiColToken)

stmtFuncCall :: Parser (Token, Int, Int) Stmt
stmtFuncCall = StmtFuncCall <$> funCall <* pToken SemiColToken

stmtReturn :: Parser (Token, Int, Int) Stmt 
stmtReturn = StmtReturn <$> ((Nothing <$ pToken ReturnToken <* pToken SemiColToken ) <|>
                            (Just <$> (pToken ReturnToken *>  expParser) <* pToken SemiColToken))

stmt :: Parser (Token, Int, Int) Stmt         
stmt = stmtReturn  <|> stmtFuncCall <|> stmtDeclareVar <|> stmtIf <|> stmtWhile

-- ===================== Expressions ============================
expId :: Parser (Token, Int, Int) Exp
expId = ExpId <$> idP <*> (Field <$> many standardFunctionP)

expInt :: Parser (Token, Int, Int) Exp
expInt = ExpInt <$> Parser (\case
              (IntToken c,line,col):xs -> Right (c,xs)
              (x, line, col):xs -> Left $ Error line col ("Expected Integer but got token: " ++ show x)
              _ -> Left $ Error 0 0 "Expected Integer but got invalid token" )

expChar :: Parser (Token, Int, Int) Exp
expChar = ExpChar <$> Parser (\case
       (CharToken c,line,col):xs -> Right (c,xs)
       (x, line, col):xs -> Left $ Error line col ("Expected Char but got token: " ++ show x)
       _ -> Left $ Error 0 0 "Expected Char but got invalid token" )

expBool :: Parser (Token, Int, Int) Exp
expBool = ExpBool <$> Parser (\case
       (BoolToken b, line, col):xs -> Right (b,xs)
       (x, line, col):xs -> Left $ Error line col ("Expected Bool but got token: " ++ show x)
       _ -> Left $ Error 0 0 "Expected Bool but got invalid token" )

expBracket :: Parser (Token, Int, Int) Exp
expBracket = pToken BrackOToken  *> expParser <* pToken BrackCToken 

pOr :: Parser (Token, Int, Int) Exp 
pOr = pChainl (op (Or <$ pToken OrToken)) pAnd

pAnd :: Parser (Token, Int, Int) Exp 
pAnd = pChainl (op (And <$ pToken AndToken)) pConst

pConst :: Parser (Token, Int, Int) Exp 
pConst = pChainl (op (Con <$ pToken ConstToken)) pComp

pComp :: Parser (Token, Int, Int) Exp 
pComp = pChainl operators pPlusMin
       where operators =    op (Le <$ pToken LeToken) <|> 
                            op (Ge <$ pToken GeToken) <|>
                            op (Eq <$ pToken EqToken) <|>
                            op (Leq <$ pToken LeqToken) <|>
                            op (Geq <$ pToken GeqToken) <|>
                            op (Leq <$ pToken LeqToken) <|>
                            op (Neq <$ pToken LeqToken)

pPlusMin :: Parser (Token, Int, Int) Exp
pPlusMin = pChainl operators pMultDivMod
       where operators = 
              op (Min <$ pToken MinToken ) <|>
              op (Plus <$ pToken PlusToken)

pMultDivMod :: Parser (Token, Int, Int) Exp
pMultDivMod = pChainl operators basicExpParser
       where operators =
              op (Mult <$ pToken MultToken ) <|> 
              op (Div <$ pToken DivToken) <|> 
              op (Mod <$ pToken ModToken)

expOp1 :: Parser (Token, Int, Int) Exp
expOp1 = ExpOp1 <$> (Neg <$ pToken MinToken <|> Not <$ pToken NotToken) <*> expParser

expEmptyList :: Parser (Token, Int, Int) Exp 
expEmptyList = ExpList [] <$ pToken EmptyListToken 

expList :: Parser (Token, Int, Int) Exp 
expList = ExpList <$> (pToken SBrackOToken *> expList <* pToken SBrackCToken)
       where expList =  (:) <$> expParser <*> many ( pToken CommaToken *> expParser)
       
expTuple :: Parser (Token, Int, Int) Exp 
expTuple = ExpTuple <$> tuple
       where tuple = pToken BrackOToken *> ((,) <$> expParser <* pToken CommaToken  <*> expParser) <* pToken BrackCToken 

expFunCall :: Parser (Token, Int, Int) Exp
expFunCall = ExpFunCall <$> funCall

basicExpParser :: Parser (Token, Int, Int) Exp 
basicExpParser = expBracket <|> expFunCall <|> expTuple <|> expList <|> expEmptyList <|> expOp1 <|> expBool <|> expChar <|> expInt <|> expId

expParser :: Parser (Token, Int, Int) Exp 
expParser = pOr

-- ===================== Field ============================
fieldP :: Parser (Token, Int, Int) Field
fieldP = Field <$> many standardFunctionP

standardFunctionP :: Parser (Token, Int, Int) StandardFunction
standardFunctionP = Head <$ pToken HdToken <|> 
                    Tail <$ pToken TlToken <|> 
                    First <$ pToken FstToken <|> 
                    Second <$ pToken SndToken <|>
                    IsEmpty <$ pToken IsEmptyToken

-- ===================== FunCall ============================
funCall :: Parser (Token, Int, Int) FunCall 
funCall = FunCall <$> idP <*> (pToken BrackOToken *> actArgs <* pToken BrackCToken)

-- ===================== ActArgs ============================
actArgs = (:) <$> expParser <*> many ( pToken CommaToken *> expParser)

-- ===================== ID ============================
idP :: Parser (Token, Int, Int) ID
idP =   Parser (\case
              (IdToken id, line, col):xs -> Right(id, xs)
              (x, line, col):xs -> Left $ Error line col ("Expected Id but got token: " ++ show x)
              _ -> Left $ Error 0 0 "Expected Id but got invalid token")

-- =====================================================
mainSegments :: Parser (Token, Int, Int) MainSegments
mainSegments = MainSegments <$> all' (FuncMain <$> funDecl <|> VarMain <$> varDecl)
         
all' :: Parser s a -> Parser s [a]
all' p = (:) <$> p <*> all p
       where all p =
              Parser $ \case
                     [] -> Right([],[])
                     xs -> run (all' p) xs

tokeniseAndParse :: Parser (Token, Int, Int) a -> [Char] -> Either Error (a, [(Token, Int, Int)])
tokeniseAndParse parser x  = runTokenise x >>= run parser

-- parseCode :: String -> Parser (Token, Int, Int) a -> Either Error (a, [(Token, Int, Int)])
-- parseCode code parser = case parseAndTokenise parser code of
--                      Right (parsed, []) -> Right (parsed, [])
--                      Right (parsed, unParsed) -> run parser unParsed
--                      x -> x

main :: IO()
main = do file <- readFile "SPL_code/main.spl"
          case tokeniseAndParse mainSegments file of 
              Right (x, _) -> do
                     exists <- doesFileExist "SPL_code/out.spl"
                     when exists $ removeFile "SPL_code/out.spl"
                     writeFile "SPL_code/out.spl"$ show x
              Left x -> do
                     print x
                     exitFailure

-- main = do file <- readFile "SPL_code/main.spl"
--           case parseCode file mainSegments of 
--               Right (x, _) -> do
--                      exists <- doesFileExist "SPL_code/out.spl"
--                      when exists $ removeFile "SPL_code/out.spl"
--                      writeFile "SPL_code/out.spl"$ show x
--               Left x -> do
--                      print x
--                      exitFailure
       -- runTokenise "\'x\'" >>= run expChar