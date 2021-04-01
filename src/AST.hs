module AST where


import Data.List ( intercalate )

newtype SPL =  SPL [Decl] 
  deriving (Show, Eq)
-- instance Show SPL where
--   show (SPL decls) = unlines $ map show decls
    -- unlines $ map show decls

data Line = Line Int Int
  deriving (Eq, Show)
-- instance Show Line where
--   show (Line ln col) = "Line " ++ show ln ++ ", Col "++ show col

data Decl = VarMain VarDecl
          | FuncMain FunDecl
          deriving (Eq, Show)
-- instance Show Decl where
--   show (VarMain x) = show x
--   show (FuncMain x) = show x  

data VarDecl = VarDeclVar ID Exp
             | VarDeclType SPLType ID Exp --Line
             deriving (Eq, Show)
-- instance Show VarDecl where
--   show (VarDeclVar i e) = "var " ++ i ++ " = "++ show e ++ ";"
--   show (VarDeclType t i e ) = show t ++ " " ++ i ++ " = "++ show e ++ ";"

data FunDecl = FunDecl ID [ID] (Maybe FunType) [VarDecl] [Stmt] --Line
             deriving (Eq, Show)
-- instance Show FunDecl where
--   show (FunDecl fName fArgs fType fVard fStmts) = 
--     fName ++ " (" ++ unwords fArgs ++ ") " ++ (case fType of 
--                                                               Just x -> ":: "++ show x
--                                                               Nothing -> "") ++ " {\n"++ 
--     prettyPrinter fVard ++ "\n" ++
--     prettyPrinter fStmts ++
--     "}"

data RetType = Void | RetSplType SPLType
  deriving (Eq)
instance Show RetType where
  show Void = "Void"
  show (RetSplType t) = show t

data FunType = FunType [SPLType] RetType 
  deriving (Eq, Show)
-- instance Show FunType where
--   show (FunType [] x) = show x
--   show (FunType l x) = concatMap ((++" ") . show) l ++ "->" ++ show x

data SPLType 
  = TypeBasic BasicType
  | TupleType (SPLType, SPLType)
  | ArrayType SPLType
  | IdType ID
  deriving (Eq, Show)
-- instance Show SPLType where
--   show (TypeBasic x) = show x
--   show (TupleType (a, b)) = "(" ++ show a ++ ","++show b ++ ")"
--   show (ArrayType x) = "["++show x++"]"
--   show (IdType id) = id

data BasicType
  = BasicInt
  | BasicBool
  | BasicChar
  deriving (Eq, Show)
-- instance Show BasicType where
--   show BasicInt = "Int"
--   show BasicBool = "Bool"
--   show BasicChar = "Char"


data Stmt = StmtIf Exp [Stmt] (Maybe [Stmt]) --Line
          | StmtWhile Exp [Stmt] --Line
          | StmtDeclareVar ID Field Exp --Line
          | StmtFuncCall FunCall --Line
          | StmtReturn (Maybe Exp) --Line
          deriving (Eq, Show)
-- instance Show Stmt where
--     show (StmtIf e ifS elseS) = 
--       "if (" ++ show e ++ ") {\n" ++ 
--         prettyPrinter ifS ++"}" ++ 
--         case elseS of
--           Just x -> " else {\n" ++ 
--             prettyPrinter x ++"}" 
--           Nothing -> ""
--     show (StmtWhile e s) = 
--       "while (" ++ show e ++ ") {\n" ++ unlines (map show s) ++"}"
--     show (StmtDeclareVar id f e) = id ++ show f ++ " = " ++ show e ++ ";"
--     show (StmtFuncCall c) = show c ++ ";"
--     show (StmtReturn e) = "return" ++ maybe "" ((" "++) . show) e ++ ";"

data Exp 
  = ExpId ID Field
  | ExpInt Integer
  | ExpChar Char
  | ExpBool Bool
  | ExpBracket Exp
  | ExpOp2 Exp Op2 Exp
  | ExpOp1 Op1 Exp
  | ExpFunCall FunCall
  | ExpEmptyList
  | ExpList [Exp]
  | ExpTuple (Exp, Exp)
  deriving(Eq, Show)
-- instance Show Exp where
--       show (ExpId s f) = s ++ show f
--       show (ExpInt i) = show i
--       show (ExpChar c) = show c
--       show (ExpBool b) = show b
--       show (ExpBracket e) = "("++show e++")"
--       show (ExpOp2 e1 op e2) = "("++show e1  ++" "++show op++" " ++ show e2++")"
--       show (ExpOp1 op e) = show op ++ show e
--       show (ExpFunCall c) = show c;
--       show (ExpList xs) =  show xs
--       show (ExpTuple t) =  "Tuple"++show t
--       show ExpEmptyList = "[]"
      
newtype Field 
  = Field [StandardFunction]
  deriving (Eq, Show)
-- instance Show Field where
--     show (Field xs) = concatMap show xs

data StandardFunction
    = Head | Tail | First | Second | IsEmpty
    deriving (Eq, Show)
-- instance Show StandardFunction where
--   show Head = ".hd"
--   show Tail = ".tl"
--   show First = ".fst"
--   show Second = ".snd"
--   show IsEmpty = ".isEmpty"

type ID = String

-- data ID = ID String Line
--   deriving (Eq)
-- instance Show ID where
--   show (ID s l) = s

data FunCall 
    = FunCall ID [Exp]
    deriving (Show, Eq)
-- instance Show FunCall where
--   show (FunCall i eS) = i ++ "("++ intercalate "," (map show eS) ++")"

-- data FunCall 
--     = FunCall String ActArgs
--     deriving (Show, Eq)

-- newtype ActArgs 
--     = ActArgs [Exp]
--     deriving (Show, Eq)

-- ==== Op1 ====
data Op1 = Neg | Not deriving (Eq, Show)
-- instance Show Op1 where
--   show Neg = "-"
--   show Not = "!"

-- ==== Op2 ====
data Op2 = Plus|Min
         |Mult|Div|Mod
         |Le|Ge|Leq|Geq|Eq|Neq
         |And|Or|Con
        deriving (Show, Eq)
-- instance Show Op2 where
--   show Plus = "+" -- Int->Int->Int
--   show Min = "-" -- Int->Int->Int
--   show Mult = "*" -- Int->Int->Int
--   show Div = "/" -- Int->Int->Int
--   show Mod = "%" -- Int->Int->Int
--   show Eq = "==" -- a->a->Bool
--   show Le = "<" -- a->a->Bool
--   show Ge = ">" -- a->a->Bool
--   show Leq = "<=" -- a->a->Bool
--   show Geq = ">=" -- a->a->Bool
--   show Neq = "!=" -- a->a->Bool
--   show And = "&&" -- Bool -> Bool -> Bool
--   show Or = "||" -- Bool -> Bool -> Bool
--   show Con = ":" -- a -> [a] -> [a]



prettyPrinter :: PrettyPrinter a => [a] -> String
prettyPrinter (x:xs) = concatMap (\x -> unlines $ map ("\t"++) (lines $ pp x)) (x:xs)
prettyPrinter [] = ""

class PrettyPrinter a where
  pp :: a -> String


-- instance PrettyPrinter a, PrettyPrinter b => PrettyPrinter (a,b) where
--   pp (x,y) = "("++ pp x ++ "," ++ pp y ++ ")"

instance PrettyPrinter SPL where
  pp (SPL decls) = unlines $ map pp decls

instance PrettyPrinter Line where
  pp (Line ln col) = "Line " ++ show ln ++ ", Col "++ show col

instance PrettyPrinter a => PrettyPrinter [a] where
    pp xs = "["++ intercalate "," (map pp xs)  ++ "]"

instance PrettyPrinter Decl where
  pp (VarMain x) = pp x
  pp (FuncMain x) = pp x  

instance PrettyPrinter VarDecl where
  pp (VarDeclVar i e) = "var " ++ i ++ " = "++ pp e ++ ";"
  pp (VarDeclType t i e ) = pp t ++ " " ++ i ++ " = "++ pp e ++ ";"

instance PrettyPrinter FunDecl where
  pp (FunDecl fName fArgs fType fVard fStmts) = 
    fName ++ " (" ++ unwords fArgs ++ ") " ++ (case fType of 
                                                              Just x -> ":: "++ pp x
                                                              Nothing -> "") ++ " {\n"++ 
    pp fVard ++ "\n" ++
    pp fStmts ++
    "}"

instance PrettyPrinter RetType where
  pp Void = "Void"
  pp (RetSplType t) = pp t

instance PrettyPrinter FunType where
  pp (FunType [] x) = pp x
  pp (FunType l x) = concatMap ((++" ") . pp) l ++ "->" ++ pp x

instance PrettyPrinter SPLType where
  pp (TypeBasic x) = pp x
  pp (TupleType (a, b)) = "(" ++ pp a ++ ","++pp b ++ ")"
  pp (ArrayType x) = "["++pp x++"]"
  pp (IdType id) = id

instance PrettyPrinter BasicType where
  pp BasicInt = "Int"
  pp BasicBool = "Bool"
  pp BasicChar = "Char"

instance PrettyPrinter Stmt where
  pp (StmtIf e ifS elseS) = 
    "if (" ++ pp e ++ ") {\n" ++ 
      prettyPrinter ifS ++"}" ++ 
      case elseS of
        Just x -> " else {\n" ++ 
          prettyPrinter x ++"}" 
        Nothing -> ""
  pp (StmtWhile e s) = 
    "while (" ++ pp e ++ ") {\n" ++ unlines (map pp s) ++"}"
  pp (StmtDeclareVar id f e) = id ++ pp f ++ " = " ++ pp e ++ ";"
  pp (StmtFuncCall c) = pp c ++ ";"
  pp (StmtReturn e) = "return" ++ maybe "" ((" "++) . pp) e ++ ";"

instance PrettyPrinter Exp where
  pp (ExpId s f) = s ++ pp f
  pp (ExpInt i) = show i
  pp (ExpChar c) = show c
  pp (ExpBool b) = show b
  pp (ExpBracket e) = "("++ pp e++")"
  pp (ExpOp2 e1 op e2) = "("++ pp e1  ++" "++ pp op++" " ++ pp e2++")"
  pp (ExpOp1 op e) = pp op ++ pp e
  pp (ExpFunCall c) = pp c;
  pp (ExpList xs) =  pp xs
  pp (ExpTuple (a,b)) =  "(" ++ pp a ++ "," ++ pp b ++")"
  pp ExpEmptyList = "[]"

instance PrettyPrinter Field where
  pp (Field xs) = concatMap pp xs

instance PrettyPrinter StandardFunction where
  pp Head = ".hd"
  pp Tail = ".tl"
  pp First = ".fst"
  pp Second = ".snd"
  pp IsEmpty = ".isEmpty"

instance PrettyPrinter FunCall where
  pp (FunCall i eS) = i ++ "("++ intercalate "," (map pp eS) ++")"

instance PrettyPrinter Op1 where
  pp Neg = "-"
  pp Not = "!"

instance PrettyPrinter Op2 where
  pp Plus = "+" -- Int->Int->Int
  pp Min = "-" -- Int->Int->Int
  pp Mult = "*" -- Int->Int->Int
  pp Div = "/" -- Int->Int->Int
  pp Mod = "%" -- Int->Int->Int
  pp Eq = "==" -- a->a->Bool
  pp Le = "<" -- a->a->Bool
  pp Ge = ">" -- a->a->Bool
  pp Leq = "<=" -- a->a->Bool
  pp Geq = ">=" -- a->a->Bool
  pp Neq = "!=" -- a->a->Bool
  pp And = "&&" -- Bool -> Bool -> Bool
  pp Or = "||" -- Bool -> Bool -> Bool
  pp Con = ":" -- a -> [a] -> [a]