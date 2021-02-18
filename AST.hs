module AST where

data VarDecl = VarDeclVar ID Exp
             | VarDeclType SPLType ID Exp

data FunDecl = FunDeclFun ID FArgs FunType [VarDecl] [Stmt]

data RetType = Void | RetSplType SPLType

data FunType = FunType [FunType] RetType

data SPLType 
  = TypeBasic BasicType
  | TupleType (SPLType, SPLType)
  | ArrayType SPLType
  | IdType ID
  deriving (Show, Eq)
          
data BasicType
  = BasicInt
  | BasicBool
  | BasicChar
  deriving (Show, Eq)

newtype FArgs = FArgs [String]

data Stmt = StmtIf Exp [Stmt] (Maybe [Stmt])
          | StmtWhile Exp [Stmt]
          | StmtDeclareVar ID Field Exp
          | StmtFuncCall FunCall
          | StmtReturn (Maybe Exp)
          deriving (Show, Eq)

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
  deriving (Show, Eq)

newtype Field 
  = Field [StandardFunctions]
  deriving (Show, Eq)

data StandardFunctions
    = Head | Tail | First | Second | IsEmpty | Print 
    deriving (Show, Eq)

type ID = String 

data FunCall 
    = FunCall String ActArgs
    deriving (Show, Eq)

newtype ActArgs 
    = ActArgs [Exp]
    deriving (Show, Eq)

-- ==== Op1 ====
data Op1 = Neg | Not deriving (Show, Eq)

-- ==== Op2 ====
data Op2 = Plus|Min
         |Mult|Div|Mod
         |Le|Ge|Leq|Geq|Eq|Neq
         |And|Or|Const
        deriving (Show, Eq)