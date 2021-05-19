{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Parser where

import Error
import Lexer
import AST

import Data.Char
import Data.Function
import Data.Functor
import Data.List

import Control.Applicative
import Control.Monad

import System.Directory
import System.Exit ( exitFailure )
import Debug.Trace

-- ======================================== Parser ========================================
newtype Parser s a = Parser {run :: [s] -> Either Error (a, [s])}
-- newtype Parser s a = Parser {runLast :: [s] -> Either Error ((a,s), [s])}
-- newtype Parser s a = Parser {run :: [s] -> Either Error (a, [s])}

-- runLast :: [s] -> Either Error ((a,s), [s])
-- runLast = Parser $ \input -> do
--     (out, input') <- p input
--     Right (f out, input')

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

(<<|>) :: Parser (Token, Loc, Loc) r -> Parser (Token, Loc, Loc) r -> Parser (Token, Loc, Loc) r
x <<|> y = Parser $ \case
  ((tokens, Loc line col, locb) : xs) ->
    case run x ((tokens, Loc line col, locb) : xs) of
      Left (Error (Loc line' col') m) | line == line' && col == col' -> run y ((tokens, Loc line col, locb) : xs)
      Left (ErrorD (DLoc (Loc line' col') _) m) | line == line' && col == col' -> run y ((tokens, Loc line col, locb) : xs)
      Left x -> Left x
      res -> res
  x -> empty

infixr 4 <|||>

(<|||>) :: Parser (a1, Int, Int) a2 -> Parser (a1, Int, Int) a2 -> Parser (a1, Int, Int) a2
x <|||> y = Parser $ \case
  ((tokens, line, col) : xs) ->
    case run x ((tokens, line, col) : xs) of
      Left (Error (Loc line' col') m) -> case run y ((tokens, line, col) : xs) of
        Left (Error (Loc line'' col'') m') -> case Error (Loc line' col') m `compare` Error (Loc line'' col'') m' of
          LT -> Left $ Error (Loc line' col') m
          GT -> Left $ Error (Loc line'' col'') m'
          EQ -> Left $ Error (Loc line' col') m
        Right x -> Right x
      Right x -> Right x
  x -> empty

pChainl :: Parser s (a -> a -> a) -> Parser s a -> Parser s a
pChainl x p = foldl (&) <$> p <*> many (flip <$> x <*> p)

op :: Parser (Token, Loc, Loc) Op2Typed -> Parser (Token, Loc, Loc) (Exp -> Exp -> Exp)
op p = lastLocExtreme $ (\a b c d -> ExpOp2 a c b d) <$> firstLocParser <*> p

lastLocExtreme :: Parser (Token, Loc, Loc) (Exp -> Exp -> Loc -> Exp) -> Parser (Token, Loc, Loc) (Exp -> Exp -> Exp)
lastLocExtreme p = Parser $ \input ->
    case run (pLastLocParser p) input of
        Right ((f,loc),remainingTokens) -> Right (\a b -> f a b loc,remainingTokens)
        Left x -> Left x


pToken :: Token -> Parser (Token, Loc, Loc) Token
pToken t = Parser $
  \case
    (x, loca, locb) : xs | x == t -> Right (x, xs)
    (x, loca, locb) : xs -> Left $ unexpectedToken t x (DLoc loca locb)
    [] -> Left $ unexpectedEOF t

pTokenLGen :: Token -> (Loc -> b) -> Parser (Token, Loc, Loc) b
pTokenLGen t f = Parser $
  \case
    (x, loca, locb) : xs | x == t -> Right (f loca, xs)
    (x, loca, locb) : xs -> Left $ unexpectedToken t x (DLoc loca locb)
    [] -> Left $ unexpectedEOF t


pTokenGen :: Token -> (Loc -> Loc -> b) -> Parser (Token, Loc, Loc) b
pTokenGen t f = Parser $
  \case
    (x, loca, locb) : xs | x == t -> Right (f loca locb, xs)
    (x, loca, locb) : xs -> Left $ unexpectedToken t x (DLoc loca locb)
    [] -> Left $ unexpectedEOF t

-- pTokenGenOffset :: Token -> (Loc -> Loc -> b) -> Int -> Parser (Token, Loc, Loc) b
-- pTokenGenOffset t f offset = Parser $
--   \case
--     (x, line, col) : xs | x == t -> Right (f (Loc line col) (Loc line (col+offset)), xs)
--     (x, line, col) : xs -> Left $ unexpectedToken t x (Loc line col)
--     [] -> Left $ unexpectedEOF t

firstLocParser :: Parser (Token, Loc, Loc) Loc
firstLocParser = Parser $
  \case
    (x, loca, locb) : xs -> Right (loca, (x, loca, locb) : xs)
    [] -> Left $ unexpectedEOF ""

lastLocParser :: Parser (Token, Loc, Loc) Loc
lastLocParser = Parser $
  \case
    (x, loca, locb) : xs -> Right (locb, (x, loca, locb) : xs)
    [] -> Left $ unexpectedEOF ""

-- ===================== VarDecl ============================
varDecl :: Parser (Token, Loc, Loc) VarDecl
varDecl =
 VarDeclType <$> rigidType <*> idPLoc <*> varAss <|> 
  VarDeclVar <$> (pToken VarToken *> idPLoc) <*> varAss
  where
    varAss = pToken IsToken *> expParser <* pToken SemiColToken

-- ===================== FunDecl ============================
funDecl :: Parser (Token, Loc, Loc) FunDecl
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
funType :: Parser (Token, Loc, Loc) (Maybe SPLType)
funType = Parser $ \case
  (FunTypeToken, loca, locb) : xs -> do
    (ys, rest) <- run (many splType) xs
    let ret = if length ys > 1 then foldr1 FunType ys else head ys
    Right (Just ret, rest)
    --undefined 
  x -> Right (Nothing, x)

-- ===== RetType =====
retType :: Parser (Token, Loc, Loc) SPLType
retType = pToken ArrowToken *> splType

voidType :: Parser (Token, Loc, Loc) SPLType
voidType = pTokenGen VoidToken Void

-- ===== Type =====
splType :: Parser (Token, Loc, Loc) SPLType
splType = rigidType <|> idType <|> voidType <|> retType

rigidType :: Parser (Token, Loc, Loc) SPLType
rigidType = typeBasic <|> tupleType <|> arrayType

typeBasic :: Parser (Token, Loc, Loc) SPLType
typeBasic = (\a (b,c) -> TypeBasic a b c ) <$> firstLocParser <*> pLastLocParser basicType

tupleType :: Parser (Token, Loc, Loc) SPLType
tupleType = (\a (b,c) -> TupleType a b c ) <$> firstLocParser <*> pLastLocParser (pToken BrackOToken *> ((,) <$> splType <* pToken CommaToken <*> splType) <* pToken BrackCToken)

arrayType :: Parser (Token, Loc, Loc) SPLType
arrayType = (\a (b,c) -> ArrayType a b c) <$> firstLocParser <*> pLastLocParser (pToken SBrackOToken *> splType <* pToken SBrackCToken)

idType :: Parser (Token, Loc, Loc) SPLType
idType = IdType <$> idPLoc

-- ===== BasicType =====
basicType :: Parser (Token, Loc, Loc) BasicType
basicType = basicInt <|> basicBool <|> basicChar

basicInt :: Parser (Token, Loc, Loc) BasicType
basicInt = BasicInt <$ pToken TypeIntToken

basicBool :: Parser (Token, Loc, Loc) BasicType
basicBool = BasicBool <$ pToken TypeBoolToken

basicChar :: Parser (Token, Loc, Loc) BasicType
basicChar = BasicChar <$ pToken TypeCharToken

-- ===================== Statements ============================
stmt :: Parser (Token, Loc, Loc) Stmt
stmt = stmtReturn <|> stmtFuncCall <|> stmtAssignVar <|> stmtIf <|> stmtWhile

stmtIf :: Parser (Token, Loc, Loc) Stmt
stmtIf =
  (\a b c d -> StmtIf b c d a)
    <$> firstLocParser
    <*> (pToken IfToken *> pToken BrackOToken *> expParser <* pToken BrackCToken)
    <*> (pToken CBrackOToken *> many' stmt <* pToken CBrackCToken)
    <*> stmtElse

stmtElse :: Parser (Token, Loc, Loc) (Maybe [Stmt])
stmtElse = Parser $ \case
  (ElseToken, line, col) : xs -> do
    (ys, rest) <- run (pToken CBrackOToken *> many' stmt <* pToken CBrackCToken) xs
    Right (Just ys, rest)
  x -> Right (Nothing, x)

stmtWhile :: Parser (Token, Loc, Loc) Stmt
stmtWhile =
  (\a b c -> StmtWhile b c a) <$> firstLocParser
    <*> (pToken WhileToken *> pToken BrackOToken *> expParser <* pToken BrackCToken)
    <*> (pToken CBrackOToken *> many' stmt <* pToken CBrackCToken)

stmtAssignVar :: Parser (Token, Loc, Loc) Stmt
stmtAssignVar =
  StmtAssignVar
    <$> idPLoc
    <*> fieldP
    <*> (pToken IsToken *> expParser <* pToken SemiColToken) 
    <*> pure Nothing

stmtFuncCall :: Parser (Token, Loc, Loc) Stmt
stmtFuncCall = flip StmtFuncCall <$> firstLocParser <*> funCall <* pToken SemiColToken

stmtReturn :: Parser (Token, Loc, Loc) Stmt
stmtReturn =
  flip StmtReturn <$> firstLocParser
    <*> ( (Nothing <$ pToken ReturnToken <* pToken SemiColToken)
            <|> (Just <$> (pToken ReturnToken *> expParser) <* pToken SemiColToken)
        )

-- ===================== Expressions ============================
expParser :: Parser (Token, Loc, Loc) Exp
expParser = pOr

expId :: Parser (Token, Loc, Loc) Exp
expId = ExpId <$> idPLoc <*> fieldP

expInt :: Parser (Token, Loc, Loc) Exp
expInt =
  Parser
    ( \case
        (IntToken i, loca, locb) : xs -> Right (ExpInt loca i locb, xs)
        (x, loca, locb) : xs -> Left $ unexpectedToken "Integer" (show x) (DLoc loca locb)
        [] -> Left $ unexpectedEOF "an Integer"
    )

expChar :: Parser (Token, Loc, Loc) Exp
expChar =
  Parser
    ( \case
        (CharToken c, loca, locb) : xs -> Right (ExpChar loca c locb, xs)
        (x, loca, locb) : xs -> Left $ unexpectedToken "Char" (show x) (DLoc loca locb)
        [] -> Left $ unexpectedEOF "an Char"
    )

expBool :: Parser (Token, Loc, Loc) Exp
expBool =
  Parser
    ( \case
        (BoolToken b, loca, locb) : xs -> Right (ExpBool loca b locb, xs)
        (x, loca, locb) : xs -> Left $ unexpectedToken "Bool" (show x) (DLoc loca locb)
        _ -> Left $ unexpectedEOF "an Bool"
    )

expBracket :: Parser (Token, Loc, Loc) Exp
expBracket = pToken BrackOToken *> expParser <* pToken BrackCToken

-- pOr :: Parser (Token, Loc, Loc) Exp
pOr :: Parser (Token, Loc, Loc) Exp
pOr = pChainl (op (op2TypedParser Or OrToken)) pAnd

pAnd :: Parser (Token, Loc, Loc) Exp
pAnd = pChainl (op (op2TypedParser And AndToken)) pConst

pConst :: Parser (Token, Loc, Loc) Exp
pConst = ((\a b c (d,e) -> ExpOp2 a b c d e)  <$> firstLocParser <*> basicExpParser <*> op2TypedParser Con ConstToken <*> pLastLocParser expParser) <|> pComp

-- pConst = pChainl (op (Con <$ pToken ConstToken)) pComp

pComp :: Parser (Token, Loc, Loc) Exp
pComp = pChainl operators pPlusMin
  where
    operators =
            op (op2TypedParser Le LeToken)
        <|> op (op2TypedParser Ge GeToken)
        <|> op (op2TypedParser Eq EqToken)
        <|> op (op2TypedParser Leq LeqToken)
        <|> op (op2TypedParser Geq GeqToken)
        <|> op (op2TypedParser Neq NeqToken)

pPlusMin :: Parser (Token, Loc, Loc) Exp
pPlusMin = pChainl operators pMultDivMod
  where
    operators =
            op (op2TypedParser Min MinToken)
        <|> op (op2TypedParser Plus PlusToken)

pMultDivMod :: Parser (Token, Loc, Loc) Exp
pMultDivMod = pChainl operators basicExpParser
  where
    operators =
            op (op2TypedParser Mult MultToken)
        <|> op (op2TypedParser Div DivToken)
        <|> op (op2TypedParser Mod ModToken)

expOp1 :: Parser (Token, Loc, Loc) Exp
expOp1 = (\a b (c,d) -> ExpOp1 a b c d)  <$> firstLocParser <*> (Neg <$ pToken MinToken <|> Not <$ pToken NotToken) <*> pLastLocParser expParser

expEmptyList :: Parser (Token, Loc, Loc) Exp
expEmptyList = pTokenGen EmptyListToken ExpEmptyList

expList :: Parser (Token, Loc, Loc) Exp
expList = (\a (b,c) -> ExpList a b c)  <$> firstLocParser <*> pLastLocParser (pToken SBrackOToken *> expList <* pToken SBrackCToken) <*> pure Nothing 
  where
    expList = customSepBy CommaToken (pToken CommaToken) expParser

expTuple :: Parser (Token, Loc, Loc) Exp
expTuple = (\a (b,c) -> ExpTuple a b c) <$> firstLocParser <*> pLastLocParser tuple <*> pure Nothing
  where
    tuple = pToken BrackOToken *> ((,) <$> expParser <* pToken CommaToken <*> expParser) <* pToken BrackCToken

expFunCall :: Parser (Token, Loc, Loc) Exp
expFunCall = (\a (b,c) -> ExpFunCall a b c  ) <$> firstLocParser <*> pLastLocParser funCall

basicExpParser :: Parser (Token, Loc, Loc) Exp
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

op2TypedParser :: Op2 -> Token -> Parser (Token, Loc, Loc) Op2Typed
op2TypedParser op token = (Op2 op Nothing <$> firstLocParser) <* pToken token

-- ===================== Field ============================
fieldP :: Parser (Token, Loc, Loc) Field
fieldP = Field <$> many standardFunctionP

standardFunctionP :: Parser (Token, Loc, Loc) StandardFunction
standardFunctionP =
  pTokenGen HdToken Head
    <|> pTokenGen TlToken Tail
    <|> pTokenGen FstToken Fst
    <|> pTokenGen SndToken Snd

-- ===================== FunCall ============================
funCall :: Parser (Token, Loc, Loc) FunCall
funCall = FunCall <$> idPLoc <*> (pToken BrackOToken *> actArgs <* pToken BrackCToken) <*> pure Nothing

-- ===================== ActArgs ============================
actArgs = customSepBy CommaToken (pToken CommaToken) expParser

-- actArgs = (:) <$> expParser <*> many' ( pToken CommaToken *> expParser)

-- ===================== ID ============================

idPLoc :: Parser (Token, Loc, Loc) IDLoc
idPLoc = Parser $ \case
    (IdToken id, loca, locb) : xs -> Right (ID loca id locb, xs)
    (x, loca, locb) : xs -> Left $ unexpectedToken "identifier (ID)" (show x) (DLoc loca locb)
    _ -> Left $ unexpectedEOF "identifier (ID)"

idP :: Parser (Token, Loc, Loc) ID
idP = Parser $ \case
    (IdToken id, loca, locb) : xs -> Right (id, xs)
    (x, loca, locb) : xs -> Left $ unexpectedToken "identifier (ID)" (show x) (DLoc loca locb)
    _ -> Left $ unexpectedEOF "identifier (ID)"

-- ========================== Helper Functions ==========================
pLastLocParser :: Parser (Token, Loc, Loc) a -> Parser (Token, Loc, Loc) (a,Loc)
pLastLocParser (Parser p) = Parser $ 
    \input -> case p input of
        Right (a,remainingTokens) -> 
            case getLastLoc input (head remainingTokens) of 
                Just loc -> return ((a,loc),remainingTokens)
                Nothing -> Left $ Error defaultLoc "Could not find last loc in parser"
        Left x -> Left x

getLastLoc :: [(Token, Loc , Loc)] -> (Token, Loc , Loc) -> Maybe Loc
getLastLoc [] _ = Nothing
getLastLoc ((_,_,alocy):(_,blocx,blocy):xs) (_,wanta,wantb) | blocx == wanta && blocy == wantb = Just alocy
getLastLoc (_:xs) x = getLastLoc xs x


-- =====================================================
mainSegments :: Parser (Token, Loc, Loc) SPL
mainSegments = SPL <$> all' (FuncMain <$> funDecl <|> VarMain <$> varDecl)

sepBy :: Parser (Token, Loc, Loc) a -> Parser (Token, Loc, Loc) b -> Parser (Token, Loc, Loc) [b]
sepBy sep elem = ((:) <$> elem <*> many (sep *> elem)) <|> pure []

customSepBy :: Token -> Parser (Token, Loc, Loc) a -> Parser (Token, Loc, Loc) b -> Parser (Token, Loc, Loc) [b]
customSepBy sepToken sep elem = Parser $ \input ->
  case run elem input of
    Right (b, input') ->
      case run sep input' of
        Right (a, input'') -> run ((b :) <$> customSepBy sepToken sep elem) input''
        Left x ->
          case run elem input' of
            Right (b', (token, _, _) : xs) -> let ((token', loca, locb) : xs) = input' in Left $ missingSeparator (DLoc loca locb) sepToken token'
            Left x -> Right ([b], input')
    Left x -> Right ([], input)

many'' :: Parser (Token, Loc, Loc) a -> Parser (Token, Loc, Loc) [a]
many'' p = ((:) <$> p <*> many p) <<|> pure []

many' :: Parser (Token, Loc, Loc) a -> Parser (Token, Loc, Loc) [a]
many' p = ((:) <$> p <*> many' p) <<|> pure []

some' :: Parser (Token, Loc, Loc) a -> Parser (Token, Loc, Loc) [a]
some' p = (:) <$> p <*> many' p

all' :: Parser s a -> Parser s [a]
all' p = (:) <$> p <*> all p
  where
    all p =
      Parser $ \case
        [] -> Right ([], [])
        xs -> run (all' p) xs

tokeniseAndParse :: Parser (Token, Loc, Loc) a -> [Char] -> Either Error (a, [(Token, Loc, Loc)])
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