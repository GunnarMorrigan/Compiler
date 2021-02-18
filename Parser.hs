newtype Parser s a = Parser {run :: [s] -> [(a, [s])]}

instance Functor (Parser s) where
    fmap f p = Parser $ \s->[(f a, ss) | (a, ss)<-run p s]

pExpr  = pChainl (op '+' <|> op '-') pFact
pFact  = pChainl (op '*' <|> op '/') pPow
pPow   =   BinOp <$> pBasic <*> symbol '^' <*> pExpr
       <|> pBasic
pBasic =   parens pExpr
       <|> Val . read <$> some pDigit
       <|> Id <$> some pAlpha