module Main (main) where

import Control.Applicative; import Control.Monad
import Data.Char
import Data.Functor; import Data.Function
import Data.List

newtype Parser s a = Parser {runParser :: [s] -> [(a, [s])]}

instance Functor (Parser s) where
    fmap f p = Parser $ \s->[(f a, ss) | (a, ss)<-runParser p s]

instance Applicative (Parser s) where
    pure a = Parser $ \s->[(a, s)]
    l <*> r = Parser $ \s->[(fa a, ss) | (fa, ss)<-runParser l s, (a, ss)<-runParser r ss]

instance Monad (Parser s) where
    ma >>= a2mb = Parser $ \s->concat [runParser (a2mb a) ss | (a, ss) <- runParser ma s]

instance Alternative (Parser s) where
    empty = Parser $ \s->[]
    l <|> r = l <<|> r --Parser $ \s->runParser l s ++ runParser r s

top :: Parser s s
top = satisfy (const True)

satisfy :: (s -> Bool) -> Parser s s
satisfy f = Parser $ \input->case input of
    (s:rest) | f s -> [(s, rest)]
    _              -> []

symbol :: Eq s => s -> Parser s s
symbol s = satisfy (== s)
{-|
infixl 3 <|>
(<|>) :: Parser s a -> Parser s a -> Parser s a
x <|> y = Parser $ \t->runParser x t ++ runParser y t
-}

pLayout :: Parser Char Char
pLayout = symbol ' ' <|> symbol '\n' <|> symbol '\t'

pDigit = satisfy isDigit
pAlpha = satisfy isAlpha
pAlnum = pDigit <|> pAlpha
{-|
infixl 4 <*>
(<*>) :: Parser s (a -> b) -> Parser s a -> Parser b
l <*> r = Parser $ \t->
    [ (fa a, ts')
    | (fa, ts ) <- runParser l t
    , ( a, ts') <- runParser r ts
    ]
pure :: a -> Parser s a
pure a = Parser $ \t->[(a, t)]

infixl 1 >>=
(>>=) :: Parser s a -> (a -> Parser s b) -> Parser s b
ma >>= a2mb = Parser $ \t->concat
    [ runParser (a2mb a) ts
    | (a, ts) <- runParser ma t
    ]
-}

pTwice :: Parser Char Char
pTwice = pAlpha >>= symbol

{-|
infixr 7 <$>
(<$>) :: (a -> b) -> Parser s a -> Parser s b
f <$> p = Parser $ \t->[(f a, ts) | (a, ts)<-runParser p t]

infixl 6 <*, *>
(<*) :: Parser s a -> Parser s b -> Parser s a
x <* y = (\x y->x) <$> x <*> y

(*>) :: Parser s a -> Parser s b -> Parser s b
x *> y = (\x y->y) <$> x <*> y

-}
parens p = symbol '(' *> p <* symbol ')'
{-|
parens  =  (+1) <$> (symbol '(' *> parens <* symbol ')')
       <|> pure 0
-}
infixr 6 <:>
(<:>) :: Parser s r -> Parser s [r] -> Parser s [r]
x <:> y = (:) <$> x <*> y
{-|
many :: Parser s r -> Parser s [r]
many p = p <:> many p <|> pure []

some :: Parser s r -> Parser s [r]
some p = p <:> many p
-}
infixr 4 <<|>
(<<|>) :: (Parser s r) -> (Parser s r) -> Parser s r
x <<|> y = Parser $ \input->case runParser x input of
    []  -> runParser y input
    res -> res

data Expr
    = BinOp Expr Char Expr
    | Val Int
    | Id String
    deriving (Show)

pExpr  = pChainl (op '+' <|> op '-') pFact
pFact :: Parser Char Expr
pFact  = pChainl (op '*' <|> op '/') pPow
pPow   =   BinOp <$> pBasic <*> symbol '^' <*> pExpr
       <|> pBasic
pBasic =   parens pExpr
       <|> Val . read <$> some pDigit
       <|> Id <$> some pAlpha

op :: Char -> Parser Char (Expr -> Expr -> Expr)
op c = (\c x y->BinOp x c y) <$> symbol c

pChainl :: Parser s (a -> a -> a) -> Parser s a -> Parser s a
pChainl op p = foldl (&) <$> p <*> many (flip <$> op <*> p)

-- instance Show Expr where
--     show (Id s) = s
--     show (Val i) = show i
--     show (BinOp l o r) = ('(':show l) ++ (o:show r) ++ ")"

main = print $ runParser ((+1) <$> top) [1 :: Int]
