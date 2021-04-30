{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Parser where

import AST
import Control.Applicative
import Control.Monad
import Data.Char
import Data.Function
import Data.Functor
import Data.List
import Data.Typeable
import Debug.Trace
import Error
import Lexer
import System.Directory
import System.Exit ( exitFailure )
import Prelude

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
    (a, b) <- run ma input
    (x, y) <- run (a2mb a) b
    Right (x, b)

-- This alternative operator tries the left side and if it can not parse anything it tries the right
-- If it can parse some tokens but then fails, it returns the error from the left.
-- Making error returning from many possible.
infixr 4 <<|>

(<<|>) :: Parser (Token, Int, Int) r -> Parser (Token, Int, Int) r -> Parser (Token, Int, Int) r
x <<|> y = Parser $ \case
  ((tokens, line, col) : xs) ->
    case run x ((tokens, line, col) : xs) of
      Left (Error line' col' m) | line == line' && col == col' -> run y ((tokens, line, col) : xs)
      Left (Error line' col' m) -> Left (Error line' col' m)
      res -> res
  x -> empty

infixr 4 <|||>

(<|||>) :: Parser (a1, Int, Int) a2 -> Parser (a1, Int, Int) a2 -> Parser (a1, Int, Int) a2
x <|||> y = Parser $ \case
  ((tokens, line, col) : xs) ->
    case run x ((tokens, line, col) : xs) of
      Left (Error line' col' m) -> case run y ((tokens, line, col) : xs) of
        Left (Error line'' col'' m') -> case Error line' col' m `compare` Error line'' col'' m' of
          LT -> Left $ Error line' col' m
          GT -> Left $ Error line'' col'' m'
          EQ -> Left $ Error line' col' m
        Right x -> Right x
      Right x -> Right x
  x -> empty

pChainl :: Parser s (a -> a -> a) -> Parser s a -> Parser s a
pChainl x p = foldl (&) <$> p <*> many (flip <$> x <*> p)

op :: Parser (Token, Int, Int) Op2 -> Parser (Token, Int, Int) (Exp -> Exp -> Exp)
op p = (\a b c d -> ExpOp2 c (Op2 b Nothing) d a) <$> locParser <*> p

pToken :: Token -> Parser (Token, Int, Int) Token
pToken t = Parser $
  \case
    (x, line, col) : xs | x == t -> Right (x, xs)
    (x, line, col) : xs -> Left $ unexpectedToken t x line col
    [] -> Left $ unexpectedEOF t

pTokenGen :: Token -> (Loc -> b) -> Parser (Token, Int, Int) b
pTokenGen t f = Parser $
  \case
    (x, line, col) : xs | x == t -> Right (f (Loc line col), xs)
    (x, line, col) : xs -> Left $ unexpectedToken t x line col
    [] -> Left $ unexpectedEOF t

locParser :: Parser (Token, Int, Int) Loc
locParser = Parser $
  \case
    (x, line, col) : xs -> Right (Loc line col, (x, line, col) : xs)
    [] -> Left $ unexpectedEOF ""

-- ===================== VarDecl ============================
varDecl :: Parser (Token, Int, Int) VarDecl
varDecl =
 VarDeclType <$> rigidType <*> idPLoc <*> varAss <|> 
  VarDeclVar <$> (pToken VarToken *> idPLoc) <*> varAss
  where
    varAss = pToken IsToken *> expParser <* pToken SemiColToken

-- ===================== FunDecl ============================
funDecl :: Parser (Token, Int, Int) FunDecl
funDecl =
  FunDecl
    <$> idPLoc
    <*> (pToken BrackOToken *> customSepBy CommaToken (pToken CommaToken) idPLoc <* pToken BrackCToken)
    <*> funType
    <*> (pToken CBrackOToken *> many' varDecl)
    <*> some stmt
    <* pToken CBrackCToken

-- ===================== Types ============================

-- ===== FunType =====
funType :: Parser (Token, Int, Int) (Maybe SPLType)
funType = Parser $ \case
  (FunTypeToken, line, col) : xs -> do
    (ys, rest) <- run (many splType) xs
    let ret = if length ys > 1 then foldr1 FunType ys else head ys
    Right (Just ret, rest)
  x -> Right (Nothing, x)

-- ===== RetType =====
retType :: Parser (Token, Int, Int) SPLType
retType = pToken ArrowToken *> splType

voidType :: Parser (Token, Int, Int) SPLType
voidType = pTokenGen VoidToken Void

-- ===== Type =====
splType :: Parser (Token, Int, Int) SPLType
splType = rigidType <|> idType <|> voidType <|> retType

rigidType :: Parser (Token, Int, Int) SPLType
rigidType = typeBasic <|> tupleType <|> arrayType

typeBasic :: Parser (Token, Int, Int) SPLType
typeBasic = flip TypeBasic <$> locParser <*> basicType

tupleType :: Parser (Token, Int, Int) SPLType
tupleType = flip TupleType <$> locParser <*> (pToken BrackOToken *> ((,) <$> splType <* pToken CommaToken <*> splType) <* pToken BrackCToken)

arrayType :: Parser (Token, Int, Int) SPLType
arrayType = flip ArrayType <$> locParser <*> (pToken SBrackOToken *> splType <* pToken SBrackCToken)

idType :: Parser (Token, Int, Int) SPLType
idType = IdType <$> idPLoc <*> pure Nothing

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
stmtIf =
  (\a b c d -> StmtIf b c d a)
    <$> locParser
    <*> (pToken IfToken *> pToken BrackOToken *> expParser <* pToken BrackCToken)
    <*> (pToken CBrackOToken *> many' stmt <* pToken CBrackCToken)
    <*> stmtElse

stmtElse :: Parser (Token, Int, Int) (Maybe [Stmt])
stmtElse = Parser $ \case
  (ElseToken, line, col) : xs -> do
    (ys, rest) <- run (pToken CBrackOToken *> many' stmt <* pToken CBrackCToken) xs
    Right (Just ys, rest)
  x -> Right (Nothing, x)

stmtWhile :: Parser (Token, Int, Int) Stmt
stmtWhile =
  (\a b c -> StmtWhile b c a) <$> locParser
    <*> (pToken WhileToken *> pToken BrackOToken *> expParser <* pToken BrackCToken)
    <*> (pToken CBrackOToken *> many' stmt <* pToken CBrackCToken)

stmtDeclareVar :: Parser (Token, Int, Int) Stmt
stmtDeclareVar =
  StmtDeclareVar
    <$> idPLoc
    <*> fieldP
    <*> (pToken IsToken *> expParser <* pToken SemiColToken)

stmtFuncCall :: Parser (Token, Int, Int) Stmt
stmtFuncCall = flip StmtFuncCall <$> locParser <*> funCall <* pToken SemiColToken

stmtReturn :: Parser (Token, Int, Int) Stmt
stmtReturn =
  flip StmtReturn <$> locParser
    <*> ( (Nothing <$ pToken ReturnToken <* pToken SemiColToken)
            <|> (Just <$> (pToken ReturnToken *> expParser) <* pToken SemiColToken)
        )

-- ===================== Expressions ============================
expParser :: Parser (Token, Int, Int) Exp
expParser = pOr

expId :: Parser (Token, Int, Int) Exp
expId = ExpId <$> idPLoc <*> fieldP

expInt :: Parser (Token, Int, Int) Exp
expInt =
  Parser
    ( \case
        (IntToken c, line, col) : xs -> Right (ExpInt c (Loc line col), xs)
        (x, line, col) : xs -> Left $ unexpectedToken "Integer" (show x) line col
        [] -> Left $ unexpectedEOF "an Integer"
    )

expChar :: Parser (Token, Int, Int) Exp
expChar =
  Parser
    ( \case
        (CharToken c, line, col) : xs -> Right (ExpChar c (Loc line col), xs)
        (x, line, col) : xs -> Left $ unexpectedToken "Char" (show x) line col
        [] -> Left $ unexpectedEOF "an Char"
    )

expBool :: Parser (Token, Int, Int) Exp
expBool =
  Parser
    ( \case
        (BoolToken b, line, col) : xs -> Right (ExpBool b (Loc line col), xs)
        (x, line, col) : xs -> Left $ unexpectedToken "Bool" (show x) line col
        _ -> Left $ unexpectedEOF "an Bool"
    )

expBracket :: Parser (Token, Int, Int) Exp
expBracket = pToken BrackOToken *> expParser <* pToken BrackCToken

-- pOr :: Parser (Token, Int, Int) Exp
pOr :: Parser (Token, Int, Int) Exp
pOr = pChainl (op (Or <$ pToken OrToken)) pAnd

pAnd :: Parser (Token, Int, Int) Exp
pAnd = pChainl (op (And <$ pToken AndToken)) pConst

pConst :: Parser (Token, Int, Int) Exp
pConst = ((\f a b c d -> f b c d a) ExpOp2 <$> locParser <*> basicExpParser <*> (Op2 Con Nothing <$ pToken ConstToken) <*> expParser) <|> pComp

-- pConst = pChainl (op (Con <$ pToken ConstToken)) pComp

pComp :: Parser (Token, Int, Int) Exp
pComp = pChainl operators pPlusMin
  where
    operators =
      op (Le <$ pToken LeToken)
        <|> op (Ge <$ pToken GeToken)
        <|> op (Eq <$ pToken EqToken)
        <|> op (Leq <$ pToken LeqToken)
        <|> op (Geq <$ pToken GeqToken)
        <|> op (Neq <$ pToken NeqToken)

pPlusMin :: Parser (Token, Int, Int) Exp
pPlusMin = pChainl operators pMultDivMod
  where
    operators =
      op (Min <$ pToken MinToken)
        <|> op (Plus <$ pToken PlusToken)

pMultDivMod :: Parser (Token, Int, Int) Exp
pMultDivMod = pChainl operators basicExpParser
  where
    operators =
      op (Mult <$ pToken MultToken)
        <|> op (Div <$ pToken DivToken)
        <|> op (Mod <$ pToken ModToken)

expOp1 :: Parser (Token, Int, Int) Exp
expOp1 = (\f a b c -> f b c a) ExpOp1 <$> locParser <*> (Neg <$ pToken MinToken <|> Not <$ pToken NotToken) <*> expParser

expEmptyList :: Parser (Token, Int, Int) Exp
expEmptyList = pTokenGen EmptyListToken ExpEmptyList

expList :: Parser (Token, Int, Int) Exp
expList = flip ExpList <$> locParser <*> (pToken SBrackOToken *> expList <* pToken SBrackCToken)
  where
    expList = customSepBy CommaToken (pToken CommaToken) expParser

expTuple :: Parser (Token, Int, Int) Exp
expTuple = flip ExpTuple <$> locParser <*> tuple
  where
    tuple = pToken BrackOToken *> ((,) <$> expParser <* pToken CommaToken <*> expParser) <* pToken BrackCToken

expFunCall :: Parser (Token, Int, Int) Exp
expFunCall = flip ExpFunCall <$> locParser <*> funCall

basicExpParser :: Parser (Token, Int, Int) Exp
basicExpParser =
  expBracket
    <|> expFunCall
    <|> expTuple
    <|> expList
    <|> expEmptyList
    <|> expOp1
    <|> expBool
    <|> expChar
    <|> expInt
    <|> expId

-- ===================== Field ============================
fieldP :: Parser (Token, Int, Int) Field
fieldP = Field <$> many standardFunctionP

standardFunctionP :: Parser (Token, Int, Int) StandardFunction
standardFunctionP =
  pTokenGen HdToken Head
    <|> pTokenGen TlToken Tail
    <|> pTokenGen FstToken First
    <|> pTokenGen SndToken Second
    <|> pTokenGen IsEmptyToken IsEmpty

-- ===================== FunCall ============================
funCall :: Parser (Token, Int, Int) FunCall
funCall = FunCall <$> idPLoc <*> (pToken BrackOToken *> actArgs <* pToken BrackCToken) <*> pure Nothing

-- ===================== ActArgs ============================
actArgs = customSepBy CommaToken (pToken CommaToken) expParser

-- actArgs = (:) <$> expParser <*> many' ( pToken CommaToken *> expParser)

-- ===================== ID ============================

idPLoc :: Parser (Token, Int, Int) IDLoc
idPLoc = Parser $ \case
  (IdToken id, line, col) : xs -> Right (ID id (Loc line col), xs)
  (x, line, col) : xs -> Left $ unexpectedToken "identifier (ID)" (show x) line col
  _ -> Left $ unexpectedEOF "identifier (ID)"

idP :: Parser (Token, Int, Int) ID
idP = Parser $ \case
  (IdToken id, line, col) : xs -> Right (id, xs)
  (x, line, col) : xs -> Left $ unexpectedToken "identifier (ID)" (show x) line col
  _ -> Left $ unexpectedEOF "identifier (ID)"

-- =====================================================
mainSegments :: Parser (Token, Int, Int) SPL
mainSegments = SPL <$> all' (FuncMain <$> funDecl <|> VarMain <$> varDecl)

sepBy :: Parser (Token, Int, Int) a -> Parser (Token, Int, Int) b -> Parser (Token, Int, Int) [b]
sepBy sep elem = ((:) <$> elem <*> many (sep *> elem)) <|> pure []

customSepBy :: Token -> Parser (Token, Int, Int) a -> Parser (Token, Int, Int) b -> Parser (Token, Int, Int) [b]
customSepBy sepToken sep elem = Parser $ \input ->
  case run elem input of
    Right (b, input') ->
      case run sep input' of
        Right (a, input'') -> run ((b :) <$> customSepBy sepToken sep elem) input''
        Left x ->
          case run elem input' of
            Right (b', (token, _, _) : xs) -> let ((token', line, col) : xs) = input' in Left $ missingSeparator line col sepToken token'
            Left x -> Right ([b], input')
    Left x -> Right ([], input)

many'' :: Parser (Token, Int, Int) a -> Parser (Token, Int, Int) [a]
many'' p = ((:) <$> p <*> many p) <<|> pure []

many' :: Parser (Token, Int, Int) a -> Parser (Token, Int, Int) [a]
many' p = ((:) <$> p <*> many' p) <<|> pure []

some' :: Parser (Token, Int, Int) a -> Parser (Token, Int, Int) [a]
some' p = (:) <$> p <*> many' p

all' :: Parser s a -> Parser s [a]
all' p = (:) <$> p <*> all p
  where
    all p =
      Parser $ \case
        [] -> Right ([], [])
        xs -> run (all' p) xs

tokeniseAndParse :: Parser (Token, Int, Int) a -> [Char] -> Either Error (a, [(Token, Int, Int)])
tokeniseAndParse parser x = runTokenise x >>= run parser

splFilePath = "../SPL_test_code/"

funTypeParser = Parser $ \case
  (FunTypeToken, line, col) : xs -> do
    (ys, rest) <- run (many splType) xs
    -- (ys, rest) <- run funType xs
    let ret = if length ys > 1 then foldr1 FunType ys else head ys
    Right (Just ret, rest)
  x -> Right (Nothing, x)

funTypeTest = tokeniseAndParse funTypeParser ":: Int Bool -> Char"

-- main :: String -> IO()
-- tokeniseAndParseFile2 filename = do
--        file <- readFile $ splFilePath++filename
--        bta (tokeniseAndParse mainSegments file) 0 empty

-- Right (x, _) -> do
--        exists <- doesFileExist "SPL_test_code/out.spl"
--        when exists $ removeFile "SPL_test_code/out.spl"
--        writeFile "SPL_test_code/out.spl"$ show x
-- Left x -> do
--        print x
--        exitFailure

tokeniseFile :: String -> IO ()
tokeniseFile filename = do
  file <- readFile $ splFilePath ++ filename
  case runTokenise file of
    Right (x : xs) -> do
      exists <- doesFileExist (splFilePath ++ "tokenOut.spl")
      when exists $ removeFile (splFilePath ++ "tokenOut.spl")
      writeFile (splFilePath ++ "tokenOut.spl") $ show (x : xs)
    Right [] -> print "No failure but nothing parsed"
    Left x -> do
      print x
      exitFailure

test = tokeniseAndParse expList "[10,10,10,]"

main :: String -> IO ()
main filename = do
  file <- readFile $ splFilePath ++ filename
  case tokeniseAndParse mainSegments file of
    Right (x, _) -> do
      exists <- doesFileExist "../SPL_test_code/out.spl"
      when exists $ removeFile "../SPL_test_code/out.spl"
      print x
      writeFile "../SPL_test_code/out.spl" $ pp x
    Left x -> do
      print x
      exitFailure

mainError filename = do
  -- path <- getCurrentDirectory
  -- print path
  file <- readFile $ splFilePath ++ filename
  case tokeniseAndParse mainSegments file of
    Right (x, _) -> putStr $ pp x
    Left x -> do
      putStr $ show x ++ "\n" ++ showPlaceOfError file x