data VarDecl = VarDeclVar String Exp
             | VarDeclType SPLType String Exp

data FunDecl = FunDeclFun String FArgs FunType [VarDecl] [Stmt]

data RetType = Void | RetSplType SPLType

data FunType = FunType [FunType] RetType

data SPLType 
  = TypeBasic BasicType
  | TupleType (SPLType, SPLType)
  | ArrayType SPLType
  | IdType String
  deriving (Show, Eq)
          
data BasicType
  = BasicInt
  | BasicBool
  | BasicChar
  deriving (Show, Eq)

newtype FArgs = FArgs [String]

data Stmt = StmtIf Exp [Stmt] (Maybe [Stmt])
          | StmtWhile Exp [Stmt]
          | StmtDeclareVar String Field Exp
          | StmtFuncCall FunCall
          | StmtReturn (Maybe Exp)
          deriving (Show, Eq)

data Exp 
  = ExpId String Field
  | ExpInt Integer
  | ExpChar Char
  | ExpBool Bool
  | ExpBracket Exp
  | ExpOp2 Exp Op2 Exp
  | ExpOp1 Op1 Exp
  | ExpFunCall FunCall
  | ExpArray [Exp]
  | ExpTuple (Exp, Exp)
  deriving (Show, Eq)

data Field 
    = Field Field [String]
    | FieldId String
    deriving (Show, Eq)

data FunCall 
    = FuncCall String ActArgs
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