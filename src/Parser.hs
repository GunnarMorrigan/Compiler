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
import Data.Either
import Data.Maybe

import Control.Applicative
import Control.Monad

import System.Directory
import System.Exit ( exitFailure )
import Debug.Trace

-- ======================================== Parser ========================================
newtype Parser s a = Parser {run :: [s] -> Either Error (a, [s])}

-- {-# ANN module "HLint: ignore" #-}
-- instance Functor (Parser s) where
--   fmap f p = do
--     out <- p
--     pure (f out)

-- instance Applicative (Parser s) where
--   pure p = Parser $ \input -> Right (p, input)
--   p1 <*> p2 = do
--     f <- p1
--     f <$> p2

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
    Right (x, y)

-- This alternative operator tries the left side and if it can not parse anything it tries the right
-- If it can parse some tokens but then fails, it returns the error from the left.
-- Making error returning from many possible.
infixr 4 <<|>
(<<|>) :: Parser (Token, Loc, Loc) r -> Parser (Token, Loc, Loc) r -> Parser (Token, Loc, Loc) r
x <<|> y = Parser $ \case
  [] -> Left trueUnexpectedEOF
  ((t,locA,locB):xs) ->
    case run x ((t,locA,locB):xs) of
      Left err1 ->
        if getFstLoc err1 == locA
            then
              run y ((t,locA,locB):xs)
            else
              Left err1
      Right x -> Right x


infixr 4 <|||>
(<|||>) :: Parser a1 a2 -> Parser a1 a2 -> Parser a1 a2
x <|||> y = Parser $ \input ->
  case run x input of
    Left err1 ->
      case run y input of
      Left err2 ->
        case getFstLoc err1 `compare` getFstLoc err2 of
          LT -> Left err1
          GT -> Left err2
          EQ -> Left err1
      Right x -> Right x
    Right x -> Right x

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
    <*> functionType
    <*> (pToken CBrackOToken *> many' varDecl)
    <*> some' stmt
    <* pToken CBrackCToken

-- ===== FunType =====
functionType :: Parser (Token, Loc, Loc) (Maybe SPLType)
functionType = Parser $ \case
  (FunTypeToken, loca, locb) : xs -> do
    (fType,ys) <- run funType xs
    Right (Just fType, ys)
  x -> Right (Nothing, x)

-- ===================== Types ============================
splType :: Parser (Token, Loc, Loc) SPLType
-- splType = rigidType <|> idType <|> voidType <|> bracketType
splType = bracketType <|> rigidType <|> idType <|> voidType

-- ===== FunType =====
-- funType :: Parser (Token, Loc, Loc) SPLType
-- funType = do
--   ys <- some'' splType
--   case length ys of
--     1 -> return $ head ys
--     _ -> return $ foldr1 FunType ys

funType :: Parser (Token, Loc, Loc) SPLType
funType = do
  locA <- firstLocParser
  ys <- many'' splType
  uncurry (FunType locA ys) <$> pLastLocParser retType
  -- ys <- many'' splType
  -- ret <- case length ys of
  --   0 -> Just <$> retType
  --   1 -> optional retType
  --   _ -> Just <$> retType
  -- let all = if isJust ret
  --     then ys ++ [fromJust ret]
  --     else ys
  -- case length all of
  --   0 -> undefined 
  --   1 -> return $ 
  --   _ -> return $ foldr1 FunType all


-- ===== RetType =====
retType :: Parser (Token, Loc, Loc) SPLType
retType = pToken ArrowToken *> splType

voidType :: Parser (Token, Loc, Loc) SPLType
voidType = pTokenGen VoidToken Void

-- ===== Type =====
rigidType :: Parser (Token, Loc, Loc) SPLType
rigidType = typeBasic <|> tupleType <|> arrayType

bracketType :: Parser (Token, Loc, Loc) SPLType
bracketType = do
  pToken BrackOToken
  t <- funType
  pToken BrackCToken
  return t
  -- if isFunctionType t
  --   then return $ BracketType t
  --   else return t


typeBasic :: Parser (Token, Loc, Loc) SPLType
typeBasic = basicInt <|> basicBool <|> basicChar

tupleType :: Parser (Token, Loc, Loc) SPLType
tupleType = (\a (b,c) -> TupleType a b c ) <$> firstLocParser <*> pLastLocParser (pToken BrackOToken *> ((,) <$> splType <* pToken CommaToken <*> splType) <* pToken BrackCToken)

arrayType :: Parser (Token, Loc, Loc) SPLType
arrayType = (\a (b,c) -> ArrayType a b c) <$> firstLocParser <*> pLastLocParser (pToken SBrackOToken *> splType <* pToken SBrackCToken)

idType :: Parser (Token, Loc, Loc) SPLType
idType = IdType <$> idPLoc

-- ===== BasicType =====
basicInt :: Parser (Token, Loc, Loc) SPLType
basicInt =  pTokenGen TypeIntToken (`TypeBasic` BasicInt)

basicBool :: Parser (Token, Loc, Loc) SPLType
basicBool = pTokenGen TypeBoolToken (`TypeBasic` BasicBool)

basicChar :: Parser (Token, Loc, Loc) SPLType
basicChar = pTokenGen TypeCharToken (`TypeBasic` BasicChar)

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
expFunCall = ExpFunCall <$> funCall

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
funCall = (\a b (c,d) -> FunCall a b c d Nothing ) <$> firstLocParser <*> idPLoc <*> pLastLocParser (pToken BrackOToken *> actArgs <* pToken BrackCToken)

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
      Right (a,[]) -> let (_,_,loc) = last input in return ((a,loc),[])
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
many'' p = ((:) <$> p <*> many p) <|||> pure []

some'' :: Parser (Token, Loc, Loc) a -> Parser (Token, Loc, Loc) [a]
some'' p = (:) <$> p <*> many'' p

--  returns error if nothing can be found basically the pure is almost always ignored
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


-- ========================== Parser Mains: ==========================
tokeniseAndParse :: Parser (Token, Loc, Loc) a -> [Char] -> Either Error (a, [(Token, Loc, Loc)])
tokeniseAndParse parser x = runTokenise x >>= run parser

splFilePath = "../SPL_test_code/"

-- funTypeTest = tokeniseAndParse funTypeParser ":: Int Bool -> Char"

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

tokeniseAndParseFile :: Show a => String -> Parser (Token, Loc, Loc) a -> IO ()
tokeniseAndParseFile filename p = do
  file <- readFile $ splFilePath ++ filename
  case tokeniseAndParse p file of
    Right (x, []) -> do
      exists <- doesFileExist (splFilePath ++ "tokenOut.spl")
      when exists $ removeFile (splFilePath ++ "tokenOut.spl")
      writeFile (splFilePath ++ "tokenOut.spl") $ show x
    Right (x,ys) -> print "No failure but nothing parsed"
    Left x -> do
      print x
      exitFailure


-- {-# NOINLINE parserTypeTests #-}
-- parserTypeTests = unsafePerformIO $ do
--     file <- readFile  "./test/parser/custom/types.spl"
--     let (errs,tokenTypes) = partitionEithers $ Prelude.map runTokenise (lines file)
--     if Prelude.null errs
--         then return $ parserTypeTest (head tokenTypes)
--         else assertFailure $ showError file (Prelude.foldr1 (<>) errs)


tokenTest = [(IdToken "a",Loc 1 1,Loc 1 2),(BrackOToken,Loc 1 3,Loc 1 4),(IdToken "c",Loc 1 4,Loc 1 5),(ArrowToken,Loc 1 6,Loc 1 8),(IdToken "d",Loc 1 9,Loc 1 10),(BrackCToken,Loc 1 10,Loc 1 11),(ArrowToken,Loc 1 12,Loc 1 14),(IdToken "b",Loc 1 15,Loc 1 16)]

test1 = case run funType tokenTest of
  Left x -> print x
  Right (t,left) -> do
    putStrLn $ pp t
    print left

pTypeTest = do
  file <- readFile  "../test/parser/custom/types.spl"
  let content = lines file
  case partitionEithers $ Prelude.map runTokenise content of
    (x:xs,_) -> do 
      putStr "ERROR\n"
      print x
    ([],x) -> sequence_ $ Prelude.map ab x 

ab x =
  case run funType x of
    Right (a,_) ->
      putStr $ "\nSuccess:\n"++ pp a ++"\n"
    Left a -> do
      putStr "\nERROR2\n"
      print x
      print a










main :: String -> IO ()
main filename = do
  file <- readFile $ splFilePath ++ filename
  case tokeniseAndParse mainSegments file of
    Right (x, _) -> do
      exists <- doesFileExist "../SPL_test_code/out.spl"
      when exists $ removeFile "../SPL_test_code/out.spl"
      putStr $ pp x
      writeFile "../SPL_test_code/out.spl" $ pp x
    Left x -> do
      print x
      exitFailure

mainParser filename = do
  -- path <- getCurrentDirectory
  -- print path
  file <- readFile $ splFilePath ++ filename
  case tokeniseAndParse mainSegments file of
    Right (x, _) -> putStr $ pp x
    Left x -> do
      putStr $ showError file x