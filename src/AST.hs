module AST where

import Data.Map as Map
import Data.List ( intercalate )

import Debug.Trace

newtype SPL =  SPL [Decl] 
  deriving (Show, Eq)

data Loc = Loc Int Int
  deriving (Eq, Show)

data Decl = VarMain VarDecl
          | FuncMain FunDecl
          | MutRec [FunDecl]
          deriving (Eq, Show)

data VarDecl = VarDeclVar IDLoc Exp
             | VarDeclType SPLType IDLoc Exp --Line
             deriving (Eq, Show)

data FunDecl = FunDecl IDLoc [IDLoc] (Maybe SPLType) [VarDecl] [Stmt] --Line
             deriving (Eq, Show)

data Class = OrdClass | EqClass deriving (Show, Eq)

data SPLType 
  = TypeBasic BasicType
  | TupleType (SPLType, SPLType)
  | ArrayType SPLType
  | IdType IDLoc (Maybe Class)
  | FunType SPLType SPLType
  | Void
  deriving (Eq, Show)

eqType :: SPLType -> SPLType -> Bool
eqType (TypeBasic l) (TypeBasic r) = l == r
eqType (TupleType (a,b)) (TupleType (c,d)) = eqType a c && eqType b d
eqType (ArrayType l) (ArrayType r) = eqType l r
eqType (IdType l c) (IdType r c') = True
eqType (FunType arg ret) (FunType arg' ret') = eqType arg arg' && eqType ret ret'
eqType Void Void = True
eqType _ _ = False


data BasicType
  = BasicInt
  | BasicBool
  | BasicChar
  deriving (Eq, Show)

data Stmt = StmtIf Exp [Stmt] (Maybe [Stmt]) --Line
          | StmtWhile Exp [Stmt] --Line
          | StmtDeclareVar IDLoc Field Exp --Line
          | StmtFuncCall FunCall --Line
          | StmtReturn (Maybe Exp) --Line
          deriving (Eq, Show)

data Exp 
  = ExpId IDLoc Field
  | ExpInt Integer
  | ExpIntLine Integer Loc
  | ExpBool Bool
  | ExpBoolLine Bool Loc
  | ExpChar Char
  | ExpCharLine Char Loc
  | ExpBracket Exp
  | ExpOp2 Exp Op2 Exp
  | ExpOp1 Op1 Exp
  | ExpFunCall FunCall
  | ExpEmptyList
  | ExpList [Exp]
  | ExpTuple (Exp, Exp)
  deriving(Eq, Show)

newtype Field
  = Field [StandardFunction]
  deriving (Eq, Show)

data StandardFunction
    = Head | Tail | First | Second | IsEmpty
    deriving (Eq, Show)

type ID = String
data IDLoc = ID String Loc
  deriving (Show, Eq)
instance Ord IDLoc where
  compare (ID id loc) (ID id' loc') = id `compare` id'

showIDLoc :: IDLoc -> String
showIDLoc (ID id (Loc line col)) | line > 0 && col > 0 = id ++ " on Line " ++ show line ++ " and, Col "++ show col++"."
showIDLoc (ID id (Loc line col)) = id

showLoc :: IDLoc -> String
showLoc (ID id (Loc line col)) = "on Line " ++ show line ++ " and, Col "++ show col

getLoc :: IDLoc -> (Int,Int)
getLoc (ID id (Loc line col)) = (line, col)

getLineNum:: IDLoc -> Int
getLineNum (ID id (Loc line col)) = line

getColNum:: IDLoc -> Int
getColNum (ID id (Loc line col)) = col

idLocCreator :: String -> IDLoc
idLocCreator s = ID s (Loc (-1) (-1))

data FunCall
    = FunCall IDLoc [Exp]
    deriving (Show, Eq)

-- ==== Op1 ====
data Op1 = Neg | Not deriving (Eq, Show)


-- ==== Op2 ====
data Op2 = Plus|Min
         |Mult|Div|Mod
         |Le|Ge|Leq|Geq|Eq|Neq
         |And|Or|Con
        deriving (Show, Eq)


-- ===================== prettyPrinter ============================

prettyPrinter :: PrettyPrinter a => [a] -> String
prettyPrinter (x:xs) = concatMap (\x -> unlines $ Prelude.map ("\t"++) (lines $ pp x)) (x:xs)
prettyPrinter [] = ""

class PrettyPrinter a where
  pp :: a -> String

instance PrettyPrinter SPL where
  pp (SPL decls) = unlines $ Prelude.map pp decls

instance PrettyPrinter Loc where
  pp (Loc ln col) = "Line " ++ show ln ++ ", Col "++ show col

instance PrettyPrinter a => PrettyPrinter [a] where
    pp xs = intercalate "\n" (Prelude.map pp xs)

instance PrettyPrinter Decl where
  pp (VarMain x) = pp x
  pp (FuncMain x) = pp x  
  pp (MutRec x) = "//MutRec" ++ prettyPrinter x

instance PrettyPrinter VarDecl where
  pp (VarDeclVar i e) = "var " ++ pp i ++ " = "++ pp e ++ ";"
  pp (VarDeclType t i e ) = pp t ++ " " ++ pp i ++ " = "++ pp e ++ ";"

instance PrettyPrinter FunDecl where
  pp (FunDecl fName fArgs fType fVard fStmts) = 
    "\n" ++ pp fName ++ " (" ++ intercalate ", " (Prelude.map pp fArgs) ++ ") " ++ (case fType of 
                                                              Just x -> ":: "++ pp x
                                                              Nothing -> "") ++ " {\n"++ 
    prettyPrinter fVard ++ (if not (Prelude.null fVard) then "\n" else "") ++
    prettyPrinter fStmts ++ 
    "}"

instance PrettyPrinter SPLType where
  pp (TypeBasic x) = pp x
  pp (TupleType (a, b)) = "(" ++ pp a ++ ", "++pp b ++ ")"
  pp (ArrayType x) = "["++pp x++"]"
  pp (IdType id Nothing) = pp id
  pp (IdType id (Just EqClass)) = "Eq "++ pp id ++ " =>" ++ pp id
  pp (IdType id (Just OrdClass)) = "Ord "++ pp id ++ " =>" ++ pp id
  -- Prints function types haskell style:
  -- pp (FunType arg ret) = ppClasses (FunType arg ret) ++ pp arg ++ " -> " ++ pp ret
  pp (FunType args ret) = 
    let types = getArgsTypes (FunType args ret) 
    in ppClasses (FunType args ret) ++ unwords (Prelude.map pp (init types)) ++ " -> " ++ pp (last types)
  pp Void = "Void"

ppClasses :: SPLType -> String
ppClasses t = let c = Map.toList (getClasses t Map.empty) in if Prelude.null c then "" else unwords (Prelude.map printClass c) ++ "=>"
  where printClass (a, EqClass) = "Eq " ++ show a
        printClass (a, OrdClass) = "Ord " ++ show a

getClasses :: SPLType -> Map.Map IDLoc Class -> Map.Map IDLoc Class
getClasses Void map = map
getClasses (TypeBasic _) map = map
getClasses (IdType id Nothing) map = map
getClasses (IdType id (Just EqClass)) map = 
  case Map.lookup id map of
    Just c -> map
    Nothing -> Map.insert id EqClass map
getClasses (IdType id (Just OrdClass)) map = Map.insert id OrdClass map
getClasses (TupleType (a,b)) map = getClasses a map `Map.union` getClasses b map
getClasses (ArrayType x) map = getClasses x map
getClasses (FunType args ret) map = getClasses args map `Map.union` getClasses ret map

-- ppArgs :: SPLType -> String
-- ppArgs (FunType args ret) = ppArgs args ++ " " ++ ppArgs ret
-- ppArgs x = pp x

getArgsTypes :: SPLType -> [SPLType]
getArgsTypes (FunType args ret) = getArgsTypes args ++ getArgsTypes ret
getArgsTypes x = [x]

instance PrettyPrinter Class where
  pp EqClass = "Eq =>"

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
    "while (" ++ pp e ++ ") {\n" ++  prettyPrinter s ++"}"
  pp (StmtDeclareVar id f e) = pp id ++ pp f ++ " = " ++ pp e ++ ";"
  pp (StmtFuncCall c) = pp c ++ ";"
  pp (StmtReturn e) = "return" ++ maybe "" ((" "++) . pp) e ++ ";"

instance PrettyPrinter Exp where
  pp (ExpId s f) = pp s ++ pp f
  pp (ExpInt i) = show i
  pp (ExpChar c) = show c
  pp (ExpBool b) = show b
  pp (ExpBracket e) = "("++ pp e++")"
  pp (ExpOp2 e1 op e2) = "("++ pp e1  ++" "++ pp op++" " ++ pp e2++")"
  pp (ExpOp1 op e) = pp op ++ pp e
  pp (ExpFunCall c) = pp c;
  pp (ExpList xs) =  "["++ intercalate "," (Prelude.map pp xs)  ++ "]"
  pp (ExpTuple (a,b)) =  "(" ++ pp a ++ ", " ++ pp b ++")"
  pp ExpEmptyList = "[]"

instance PrettyPrinter Field where
  pp (Field xs) = concatMap pp xs

instance PrettyPrinter StandardFunction where
  pp Head = ".hd"
  pp Tail = ".tl"
  pp First = ".fst"
  pp Second = ".snd"
  pp IsEmpty = ".isEmpty"

instance PrettyPrinter IDLoc where
  pp (ID  id (Loc line col)) = id

instance PrettyPrinter FunCall where
  pp (FunCall i eS) = pp i ++ "("++ intercalate "," (Prelude.map pp eS) ++")"

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