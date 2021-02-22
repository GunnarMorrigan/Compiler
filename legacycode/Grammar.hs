import Control.Applicative
import Data.Char


-- ======================================== SPL Grammar ========================================

data VarDecl = VarDeclVar String Exp
             | VarDeclType SPLType String Exp

-- ==== FunDecl ====
data FunDecl = FunDeclFun String FArgs FunType [VarDecl] [Stmt]

-- ==== RetType ====
-- Nothing is 'Void'
newtype RetType = Maybe SPLType

-- ==== FunType ====
data FunType = FunType FTypes RetType

-- ==== FTypes ====
newtype FTypes = FTypes [SPLType]

-- ==== Type ====
data SPLType 
  = TypeBasic BasicType
  | TupleType (SPLType, SPLType)
  | ArrayType SPLType
  deriving (Show, Eq)

-- ==== BasicType ====
data BasicType
  = BasicInt
  | BasicBool
  | BasicChar
  deriving (Show, Eq)

-- ==== FArgs ====
newtype FArgs = FArgs [String]

-- ==== Stmt ====
data Stmt = StmtIf Exp [Stmt] (Maybe [Stmt])
          | StmtWhile Exp [Stmt]
          | StmtReturn (Maybe Exp)
          deriving (Show, Eq)

-- ==== Exp ====
data HigherExp
    = ExpOp1 Op1 HigherExp
    | ExpOr OrExp 
    | ExpOrRec OrExp HigherExp
  deriving(Show, Eq)

data OrExp 
    = ExpAnd AndExp
    | ExpAndRec AndExp OrExp
    deriving(Show, Eq)

data AndExp 
    = ExpConst ConstExp 
    | ExpConstRec ConstExp AndExp
    deriving (Show, Eq)

data ConstExp 
    = ExpComp CompExp 
    | ExpCompRec CompExp OpComp ConstExp
    deriving (Show, Eq)

-- Le, Ge, Leq, Geq, Eq and Neq
data CompExp
    = ExpPlusMin PlusMinExp
    | ExpPlusMinRec PlusMinExp CompExp
    deriving (Show, Eq)

data PlusMinExp
    = PlusMinExp MultDivModExp [(OpPre4, MultDivModExp)]
    deriving (Show, Eq)

data MultDivModExp
    = MultDivModExp Exp [(OpPre3, Exp)]
    deriving (Show, Eq)

data Exp 
  = ExpId String Field
  | ExpInt Integer
  | ExpChar Char
  | ExpBool Bool
  | ExpBracket Exp
  | ExpFunCall FunCall
  | ExpEmptyList
  | ExpTuple (Exp, Exp)
  deriving (Show, Eq)

-- === Field ===
data Field =  Field Field String
              | ExpField Exp
            deriving (Show, Eq)
            
-- === FunCall ===
data FunCall = FunCall String ActArgs
        deriving (Show, Eq)

-- === ActArgs ===
newtype ActArgs = Actargs [HigherExp]
  deriving (Show, Eq)

-- ==== Op2 ====
data OpPre3 = Mult|Div|Mod deriving (Show, Eq)
data OpPre4 = Plus|Min deriving (Show, Eq)
data OpComp = Le|Ge|Leq|Geq|Eq|Neq deriving (Show, Eq)
data OpCon = Con deriving (Show, Eq)
-- Not needed
-- data OpPre11 = And deriving (Show, Eq)
-- data OpPre12 = Or deriving (Show, Eq)

-- ==== Op1 ====
data Op1 = Neg | Not deriving (Show, Eq)
