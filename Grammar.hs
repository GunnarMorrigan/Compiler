import Control.Applicative
import Data.Char


-- ======================================== SPL Grammar ========================================

data VarDecl = VarDeclVar String Exp
             | VarDeclType SPLType String Exp

data FunDecl = FunDeclFun String Fargs FunType [VarDecl] [Stmt]

data FunType = P

data FTypes = Undef

data SPLType 
  = TypeBasic BasicType
  | TupleType (SPLType, SPLType)
  | ArrayType SPLType
  deriving (Show, Eq)
          
data BasicType
  = BasicInt
  | BasicBool
  | BasicChar
  deriving (Show, Eq)

data Fargs = Hallo

data Stmt = StmtIf Exp [Stmt] (Maybe [Stmt])
          | StmtWhile Exp [Stmt]
          | StmtReturn (Maybe Exp)
          deriving (Show, Eq)

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

data OpCon = Con deriving (Show, Eq)
data Op1 = Neg | Not deriving (Show, Eq)

-- ==== Op2 ====
data OpPre3 = Mult|Div|Mod deriving (Show, Eq)
data OpPre4 = Plus|Min deriving (Show, Eq)
data OpComp = Le|Ge|Leq|Geq|Eq|Neq deriving (Show, Eq)

-- Not needed
-- data OpPre11 = And deriving (Show, Eq)
-- data OpPre12 = Or deriving (Show, Eq)

-- ========

data Field = Fjeld
            deriving (Show, Eq)

data FunCall = CallFun
        deriving (Show, Eq)