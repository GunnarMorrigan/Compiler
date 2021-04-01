{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Parser where 

import Lexer
import AST

import Prelude
import Control.Monad
import Control.Applicative
import Data.Char
import Data.List
import Data.Functor
import Data.Typeable
import Data.Function
import Debug.Trace
import System.Exit
import System.Directory


-- ======================================== Parser ========================================
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

-- This alternative operator tries the left side and if it can not parse anything it tries the right
-- If it can parse some tokens but then fails, it returns the error from the left.
-- Making error returning from many possible.
infixr 4 <<|>
(<<|>) :: Parser (Token, Int, Int) r -> Parser (Token, Int, Int) r -> Parser (Token, Int, Int) r
x <<|> y = Parser $ \case 
       ((tokens, line, col):xs) -> 
              case run x ((tokens, line, col):xs) of
                     Left (Error line' col' m) | line==line' && col==col' -> run y ((tokens, line, col):xs)
                     Left (Error line' col' m) -> Left (Error line' col' m)
                     res -> res
       x -> empty

pChainl :: Parser s (a -> a -> a) -> Parser s a -> Parser s a
pChainl x p = foldl (&) <$> p <*> many (flip <$> x <*> p)

op :: Parser (Token, Int, Int) Op2 -> Parser (Token, Int, Int) (Exp -> Exp -> Exp)
op p = flip ExpOp2 <$> p

pToken :: Token -> Parser (Token, Int, Int) Token
pToken t = Parser $ 
       \case 
              (x, line, col):xs | x == t -> Right (x,xs)
              (x, line, col):xs -> Left $ Error line col ("Expected: '"++show t++"' but found: " ++ show x)
              [] -> Left $ Error (-1) (-1) ("Unexpected EOF, expected: '"++show t++"'")

-- ===================== VarDecl ============================
varDecl :: Parser (Token, Int, Int) VarDecl 
varDecl = VarDeclType <$> splType <*> idP <*> varAss <|>
          (VarDeclVar <$> (pToken VarToken *> idP) <*> varAss)
              where varAss = pToken IsToken *> expParser <* pToken SemiColToken

-- ===================== FunDecl ============================ 
funDecl :: Parser (Token, Int, Int) FunDecl
funDecl = FunDecl <$> 
       idP <*> 
       (pToken BrackOToken *> sepBy (pToken CommaToken ) idP <* pToken BrackCToken) <*>
       funTypeOptional <*>
       (pToken CBrackOToken*> many varDecl) <*>
       some stmt 
       <* pToken CBrackCToken
 where funTypeOptional = Parser $ \case
                     (FunTypeToken, line, col): xs -> do
                            (ys, rest) <- run funType xs
                            Right (Just ys, rest)
                     x -> Right (Nothing, x)

-- ===================== Types ============================
-- ===== FunType =====
funType :: Parser (Token, Int, Int) FunType 
funType = FunType <$> many splType <*> (pToken ArrowToken *> retType)

-- ===== RetType =====
retType :: Parser (Token, Int, Int) RetType
retType = RetSplType <$> splType <|> Void <$ pToken VoidToken

-- ===== Type =====
splType :: Parser (Token, Int, Int) SPLType 
splType = (TypeBasic <$> basicType) <|> tupleType <|> arrayType <|> idType

tupleType :: Parser (Token, Int, Int) SPLType 
tupleType = TupleType <$> ( pToken BrackOToken *> ((,) <$> splType <* pToken CommaToken  <*> splType) <* pToken BrackCToken)

arrayType :: Parser (Token, Int, Int) SPLType
arrayType = ArrayType <$> (pToken SBrackOToken *> splType <* pToken SBrackCToken)

idType :: Parser (Token, Int, Int) SPLType 
idType = IdType <$> idP

-- ===== BasicType =====
basicType :: Parser (Token, Int, Int) BasicType
basicType = basicInt <|> basicBool <|> basicChar 

basicInt :: Parser (Token, Int, Int) BasicType
basicInt = BasicInt <$ pToken TypeIntToken

basicBool :: Parser (Token, Int, Int) BasicType
basicBool = BasicBool <$ pToken TypeBoolToken

basicChar :: Parser (Token, Int, Int) BasicType
basicChar = BasicChar <$ pToken TypeCharToken

-- ===================== Statements ============================
stmt :: Parser (Token, Int, Int) Stmt         
stmt = stmtReturn <|> stmtFuncCall <|> stmtDeclareVar <|> stmtIf <|> stmtWhile

stmtIf :: Parser (Token, Int, Int) Stmt
stmtIf = StmtIf <$> 
       (pToken IfToken *> pToken BrackOToken *> expParser <* pToken BrackCToken) <*>
       (pToken CBrackOToken *> many' stmt <* pToken CBrackCToken) <*> 
       stmtElse

stmtElse :: Parser (Token, Int, Int) (Maybe [Stmt])
stmtElse = Parser $ \case
       (ElseToken,line,col):xs -> do
              (ys,rest) <- run (pToken CBrackOToken *> many' stmt <* pToken CBrackCToken) xs
              Right (Just ys, rest)
       x -> Right (Nothing,x)

stmtWhile :: Parser (Token, Int, Int) Stmt
stmtWhile = StmtWhile <$> 
       (pToken WhileToken *> pToken BrackOToken *> expParser <* pToken BrackCToken) <*>
       (pToken CBrackOToken *>  many' stmt <* pToken CBrackCToken) 

stmtDeclareVar :: Parser (Token, Int, Int) Stmt
stmtDeclareVar = StmtDeclareVar <$> 
       idP <*> 
       fieldP <*> 
       (pToken IsToken *> expParser <* pToken SemiColToken)

stmtFuncCall :: Parser (Token, Int, Int) Stmt
stmtFuncCall = StmtFuncCall <$> funCall <* pToken SemiColToken

stmtReturn :: Parser (Token, Int, Int) Stmt 
stmtReturn = StmtReturn <$> 
       ((Nothing <$ pToken ReturnToken <* pToken SemiColToken ) <|>
       (Just <$> (pToken ReturnToken *> expParser) <* pToken SemiColToken))

-- ===================== Expressions ============================
expParser :: Parser (Token, Int, Int) Exp 
expParser = pOr

expId :: Parser (Token, Int, Int) Exp
expId = ExpId <$> idP <*> fieldP

-- expInt1 :: Parser (Token, Int, Int) Exp
-- expInt1 = ExpInt <$> Parser 
--        (\case
--               (IntToken c,line,col):xs -> Right (c,xs)
--               (x, line, col):xs -> Left $ Error line col ("Expected Integer but got token: " ++ show x)
--               _ -> Left $ Error 0 0 "Expected Integer but got invalid token" )

expInt :: Parser (Token, Int, Int) Exp
expInt = ExpInt <$> Parser 
       (\case
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
pConst = (ExpOp2 <$> basicExpParser <*> (Con <$ pToken ConstToken) <*> expParser) <|> pComp
-- pConst = pChainl (op (Con <$ pToken ConstToken)) pComp

pComp :: Parser (Token, Int, Int) Exp 
pComp = pChainl operators pPlusMin
       where operators =
              op (Le <$ pToken LeToken) <|> 
              op (Ge <$ pToken GeToken) <|>
              op (Eq <$ pToken EqToken) <|>
              op (Leq <$ pToken LeqToken) <|>
              op (Geq <$ pToken GeqToken) <|>
              op (Neq <$ pToken NeqToken)

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
expEmptyList = ExpEmptyList <$ pToken EmptyListToken

expList :: Parser (Token, Int, Int) Exp 
expList = ExpList <$> (pToken SBrackOToken *> expList <* pToken SBrackCToken)
       where expList = sepBy (pToken CommaToken) expParser
       
expTuple :: Parser (Token, Int, Int) Exp 
expTuple = ExpTuple <$> tuple
       where tuple = pToken BrackOToken *> ((,) <$> expParser <* pToken CommaToken  <*> expParser) <* pToken BrackCToken 

expFunCall :: Parser (Token, Int, Int) Exp
expFunCall = ExpFunCall <$> funCall

basicExpParser :: Parser (Token, Int, Int) Exp 
basicExpParser = 
       expBracket <|>
       expFunCall <|>
       expTuple <|>
       expList <|>
       expEmptyList <|>
       expOp1 <|>
       expBool <|>
       expChar <|>
       expInt <|>
       expId

-- ===================== Field ============================
fieldP :: Parser (Token, Int, Int) Field
fieldP = Field <$> many standardFunctionP

standardFunctionP :: Parser (Token, Int, Int) StandardFunction
standardFunctionP = 
       Head <$ pToken HdToken <|> 
       Tail <$ pToken TlToken <|> 
       First <$ pToken FstToken <|> 
       Second <$ pToken SndToken <|>
       IsEmpty <$ pToken IsEmptyToken

-- ===================== FunCall ============================
funCall :: Parser (Token, Int, Int) FunCall 
funCall = FunCall <$> idP <*> (pToken BrackOToken *> actArgs <* pToken BrackCToken)

-- ===================== ActArgs ============================
actArgs = sepBy (pToken CommaToken) expParser
-- actArgs = (:) <$> expParser <*> many' ( pToken CommaToken *> expParser)

-- ===================== ID ============================
idP :: Parser (Token, Int, Int) ID
idP =   Parser $ \case
       (IdToken id, line, col):xs -> Right(id, xs)
       (x, line, col):xs -> Left $ Error line col ("Expected Id but got token: " ++ show x)
       _ -> Left $ Error 0 0 "Expected Id but got invalid token"

-- idP :: Parser (Token, Int, Int) ID
-- idP =   Parser $ \case
--        (IdToken id, line, col):xs -> Right( ID id (Line line col), xs)
--        (x, line, col):xs -> Left $ Error line col ("Expected Id but got token: " ++ show x)
--        _ -> Left $ Error 0 0 "Expected Id but got invalid token"

-- =====================================================
mainSegments :: Parser (Token, Int, Int) SPL
mainSegments = SPL <$> all' (FuncMain <$> funDecl <|> VarMain <$> varDecl)

sepBy :: Parser (Token, Int, Int) a -> Parser (Token, Int, Int) b -> Parser (Token, Int, Int) [b]
sepBy sep elem = ((:) <$> elem <*> many (sep *> elem)) <|> pure []

many' :: Parser (Token, Int, Int) a -> Parser (Token, Int, Int) [a]
many' p = ((:) <$> p <*> many' p) <<|> pure []

some' :: Parser (Token, Int, Int) a -> Parser (Token, Int, Int) [a]
some' p = (:) <$> p <*> many' p

all' :: Parser s a -> Parser s [a]
all' p = (:) <$> p <*> all p
       where all p =
              Parser $ \case
                     [] -> Right([],[])
                     xs -> run (all' p) xs

tokeniseAndParse :: Parser (Token, Int, Int) a -> [Char] -> Either Error (a, [(Token, Int, Int)])
tokeniseAndParse parser x  = runTokenise x >>= run parser

splFilePath = "../SPL_code/"


-- main :: String -> IO()
-- tokeniseAndParseFile2 filename = do
--        file <- readFile $ splFilePath++filename
--        bta (tokeniseAndParse mainSegments file) 0 empty
       
              -- Right (x, _) -> do
              --        exists <- doesFileExist "SPL_code/out.spl"
              --        when exists $ removeFile "SPL_code/out.spl"
              --        writeFile "SPL_code/out.spl"$ show x
              -- Left x -> do
              --        print x
              --        exitFailure

tokeniseFile :: String -> IO()
tokeniseFile filename = do
       file <- readFile $ splFilePath++filename
       case runTokenise file of 
              Right (x:xs) -> do
                     exists <- doesFileExist (splFilePath++"tokenOut.spl")
                     when exists $ removeFile (splFilePath++"tokenOut.spl")
                     writeFile (splFilePath++"tokenOut.spl") $ show (x:xs)
              Right [] -> print "No failure but nothing parsed" 
              Left x -> do
                     print x
                     exitFailure

test = tokeniseAndParse expList "[10,10,10,]"

main :: String -> IO()
main filename = do
       file <- readFile $ splFilePath++filename
       case tokeniseAndParse mainSegments file of 
              Right (x, _) -> do
                     exists <- doesFileExist "SPL_code/out.spl"
                     when exists $ removeFile "SPL_code/out.spl"
                     writeFile "SPL_code/out.spl"$ pp x
              Left x -> do
                     print x
                     exitFailure
