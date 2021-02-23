module AST where


import Data.List ( intercalate )

newtype SPL =  SPL [Decl] deriving (Eq)
instance Show SPL where
  show (SPL decls) = unlines $ map show decls
    -- unlines $ map show decls

data Decl = VarMain VarDecl
          | FuncMain FunDecl
          deriving (Eq)
instance Show Decl where
  show (VarMain x) = show x
  show (FuncMain x) = show x  

data VarDecl = VarDeclVar ID Exp
             | VarDeclType SPLType ID Exp
             deriving (Eq)
instance Show VarDecl where
  show (VarDeclVar i e) = "var " ++ i ++ " = "++ show e ++ ";"
  show (VarDeclType t i e) = show t ++ " " ++ i ++ " = "++ show e ++ ";"

data FunDecl = FunDecl ID [ID] (Maybe FunType) [VarDecl] [Stmt]
             deriving (Eq)
instance Show FunDecl where
  show (FunDecl fName fArgs fType fVard fStmts) = 
    fName ++ " (" ++ unwords fArgs ++ ") " ++ (case fType of  Just x -> ":: "++show x
                                                              Nothing -> "") ++ " {\n"++ 
    prettyPrinter fVard ++ "\n" ++
    prettyPrinter fStmts ++
    "}"

prettyPrinter :: Show a => [a] -> String
prettyPrinter (x:xs) = concatMap (\x -> unlines $ map ("\t"++) (lines $ show x)) (x:xs)
prettyPrinter [] = ""

data RetType = Void | RetSplType SPLType
  deriving (Eq)
instance Show RetType where
  show Void = "Void"
  show (RetSplType t) = show t

data FunType = FunType [SPLType] RetType 
  deriving (Eq)
instance Show FunType where
  show (FunType [] x) = show x
  show (FunType l x) = concatMap ((++" ") . show) l ++ "->" ++ show x

data SPLType 
  = TypeBasic BasicType
  | TupleType (SPLType, SPLType)
  | ArrayType SPLType
  | IdType ID
  deriving (Eq)
instance Show SPLType where
  show (TypeBasic x) = show x
  show (TupleType (a, b)) = "(" ++ show a ++ ","++show b ++ ")"
  show (ArrayType x) = "["++show x++"]"
  show (IdType id) = id

data BasicType
  = BasicInt
  | BasicBool
  | BasicChar
  deriving (Eq)
instance Show BasicType where
  show BasicInt = "Int"
  show BasicBool = "Bool"
  show BasicChar = "Char"


data Stmt = StmtIf Exp [Stmt] (Maybe [Stmt])
          | StmtWhile Exp [Stmt]
          | StmtDeclareVar ID Field Exp
          | StmtFuncCall FunCall
          | StmtReturn (Maybe Exp)
          deriving (Eq)
instance Show Stmt where
    show (StmtIf e ifS elseS) = 
      "if (" ++ show e ++ ") {\n" ++ 
        prettyPrinter ifS ++"}" ++ 
        case elseS of
          Just x -> " else {\n" ++ 
            prettyPrinter x ++"}" 
          Nothing -> ""
    show (StmtWhile e s) = 
      "while (" ++ show e ++ ") {\n" ++ unlines (map show s) ++"}"
    show (StmtDeclareVar id f e) = id ++ show f ++ " = " ++ show e ++ ";"
    show (StmtFuncCall c) = show c ++ ";"
    show (StmtReturn e) = "return" ++ maybe "" ((" "++) . show) e ++ ";"

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
  deriving(Eq)
instance Show Exp where
      show (ExpId s f) = s ++ show f
      show (ExpInt i) = show i
      show (ExpChar c) = show c
      show (ExpBool b) = show b
      show (ExpBracket e) = "("++show e++")"
      show (ExpOp2 e1 op e2) = "("++show e1  ++" "++show op++" " ++ show e2++")"
      show (ExpOp1 op e) = show op ++ show e
      show (ExpFunCall c) = show c;
      show (ExpList xs) =  show xs
      show (ExpTuple t) =  "Tuple"++show t
      show ExpEmptyList = "[]"
      
newtype Field 
  = Field [StandardFunction]
  deriving (Eq)
instance Show Field where
    show (Field xs) = concatMap show xs

data StandardFunction
    = Head | Tail | First | Second | IsEmpty
    deriving (Eq)
instance Show StandardFunction where
  show Head = ".hd"
  show Tail = ".tl"
  show First = ".fst"
  show Second = ".snd"
  show IsEmpty = ".isEmpty"

type ID = String 

data FunCall 
    = FunCall ID [Exp]
    deriving (Eq)
instance Show FunCall where
  show (FunCall i eS) = i++"("++ intercalate "," (map show eS) ++")"

-- data FunCall 
--     = FunCall String ActArgs
--     deriving (Show, Eq)

-- newtype ActArgs 
--     = ActArgs [Exp]
--     deriving (Show, Eq)

-- ==== Op1 ====
data Op1 = Neg | Not deriving (Eq)
instance Show Op1 where
  show Neg = "-"
  show Not = "!"

-- ==== Op2 ====
data Op2 = Plus|Min
         |Mult|Div|Mod
         |Le|Ge|Leq|Geq|Eq|Neq
         |And|Or|Con
        deriving (Eq)
instance Show Op2 where
  show Plus = "+"
  show Min = "-"
  show Mult = "*"
  show Div = "/"
  show Mod = "%"
  show Eq = "=="
  show Le = "<"
  show Ge = ">"
  show Leq = "<="
  show Geq = ">="
  show Neq = "!="
  show And = "&&"
  show Or = "||"
  show Con = ":"