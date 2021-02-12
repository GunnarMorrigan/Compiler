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

-- data Exp 
--   = ExpId String Field
--   | ExpInt Integer
--   | ExpChar Char
--   | ExpBool Bool
--   | ExpBracket Exp
--   | ExpOp2 Exp Op2 Exp
--   | ExpOp1 Op1 Exp
--   | ExpFunCall FunCall
--   | ExpArray [Exp]
--   | ExpTuple (Exp, Exp)
--   deriving (Show, Eq)

data HigherExp
    = OrExp HigherExp OpPre12 AndExp 
    | NextOrExp AndExp
    deriving(Show, Eq)

data Exp 
  = ExpId String Field
  | ExpInt Integer
  | ExpChar Char
  | ExpBool Bool
  | ExpBracket Exp
  | ExpOp1 Op1 Exp
  | ExpFunCall FunCall
  | ExpArray [Exp]
  | ExpTuple (Exp, Exp)
  deriving (Show, Eq)
      
data AndExp 
    = AndExp AndExp OpPre11 CompExp
    | NextAndExp CompExp
    deriving (Show, Eq)

-- Le, Ge, Leq, Geq, Eq and Neq
data CompExp
    = LeGeExp CompExp OpPre6 PlusMinExp
    | NextLeGeExp PlusMinExp
    deriving (Show, Eq)

data PlusMinExp 
    = PlusMinExp MultDivModExp [(OpPre4, PlusMinExp)]
    | NextPlusMinExp  MultDivModExp
    deriving (Show, Eq)

data MultDivModExp
    = MultDivModExp ConExp [(OpPre3, MultDivModExp)]
    | NextMultDivModExp ConExp
    deriving (Show, Eq)

data ConExp 
    = ConExp ConExp OpCon Exp
    | RecExp HigherExp
    deriving (Show, Eq)

data OpCon = Con deriving (Show, Eq)
data Op1 = Neg | Not deriving (Show, Eq)

-- ==== Op2 ====
data OpPre3 = Mult|Div|Mod deriving (Show, Eq)
data OpPre4 = Plus|Min deriving (Show, Eq)
data OpPre6 = Le|Ge|Leq|Geq|Eq|Neq deriving (Show, Eq)

data OpPre11 = And deriving (Show, Eq)
data OpPre12 = Or deriving (Show, Eq)

-- ========

data Field = Fjeld
            deriving (Show, Eq)

data FunCall = CallFun
        deriving (Show, Eq)