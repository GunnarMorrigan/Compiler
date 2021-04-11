module AST where

import Error

import Data.Map as Map
import Data.List ( intercalate )

import Debug.Trace

newtype SPL =  SPL [Decl] 
  deriving (Show, Eq)


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
  = TypeBasic BasicType Loc
  | TupleType (SPLType, SPLType) Loc
  | ArrayType SPLType Loc
  | IdType IDLoc (Maybe Class)
  | FunType SPLType SPLType
  | Void Loc
  deriving (Eq, Show)

eqType :: SPLType -> SPLType -> Bool
eqType (TypeBasic l loc) (TypeBasic r loc') = l == r
eqType (TupleType (a,b) loc) (TupleType (c,d) loc') = eqType a c && eqType b d
eqType (ArrayType a loc) (ArrayType b loc') = eqType a b
eqType (IdType l c) (IdType r c') = True
eqType (FunType arg ret) (FunType arg' ret') = eqType arg arg' && eqType ret ret'
eqType (Void x) (Void x') = True
eqType _ _ = False


data BasicType
  = BasicInt
  | BasicBool
  | BasicChar
  deriving (Eq, Show)

data Stmt = StmtIf Exp [Stmt] (Maybe [Stmt]) --Line
          | StmtWhile Exp [Stmt] --Line
          | StmtDeclareVar IDLoc Field Exp --Line
          | StmtFuncCall FunCall Loc --Line
          | StmtReturn (Maybe Exp) Loc --Line
          deriving (Eq, Show)

data Exp 
  = ExpId IDLoc Field
  | ExpInt Integer
  | ExpIntLine Integer Loc -- remove
  | ExpBool Bool
  | ExpBoolLine Bool Loc -- remove
  | ExpChar Char
  | ExpCharLine Char Loc -- remove
  | ExpBracket Exp
  | ExpOp2 Exp Op2 Exp -- Loc
  | ExpOp1 Op1 Exp -- Loc 
  | ExpFunCall FunCall -- Loc
  | ExpEmptyList -- Loc
  | ExpList [Exp] Loc -- Loc
  | ExpTuple (Exp, Exp) -- Loc
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


-- ===================== Loc ============================

class LOC a where
  showLoc :: a -> String
  getLoc :: a -> Loc
  getLineNum:: a -> Int
  getColNum:: a -> Int

instance LOC Loc where
  showLoc (Loc line col) = "on Line " ++ show line ++ " and, Col "++ show col
  getLoc x = x
  getLineNum (Loc line col) = line
  getColNum (Loc line col) = col

instance LOC IDLoc where
  showLoc (ID id loc) = showLoc loc
  getLoc (ID id loc) = getLoc loc
  getLineNum (ID id loc) = getLineNum loc 
  getColNum (ID id loc) = getColNum loc 

showIDLoc :: IDLoc -> String
showIDLoc (ID id (Loc line col)) | line > 0 && col > 0 = id ++ " on Line " ++ show line ++ " and, Col "++ show col++"."
showIDLoc (ID id (Loc line col)) = id

idLocCreator :: String -> IDLoc
idLocCreator s = ID s (Loc (-1) (-1))

instance LOC SPLType where
  showLoc x = let Loc line col = getLoc x in "on Line " ++ show line ++ " and, Col "++ show col

  getLoc (TypeBasic _ loc) = loc
  getLoc (ArrayType _ loc) =  loc
  getLoc (TupleType _ loc) =  loc
  getLoc (IdType idloc _) =  getLoc idloc
  getLoc (Void loc) = loc

  getLineNum (TypeBasic _ loc) = getLineNum loc
  getLineNum (ArrayType _ loc) = getLineNum loc
  getLineNum (TupleType _ loc) = getLineNum loc
  getLineNum (IdType idloc _) = getLineNum idloc
  getLineNum (Void loc) = getLineNum loc

  getColNum (ArrayType _ loc) = getColNum loc
  getColNum (TupleType _ loc) = getColNum loc
  getColNum (TypeBasic _ loc) = getColNum loc
  getColNum (IdType idloc _) = getColNum idloc
  getColNum (Void loc) = getColNum loc

-- ===================== FunCall and Operators ============================

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
  pp (TypeBasic x loc) = pp x
  pp (TupleType (a, b) loc) = "(" ++ pp a ++ ", "++pp b ++ ")"
  pp (ArrayType x loc) = "["++pp x++"]"
  pp (IdType id Nothing) = pp id
  pp (IdType id (Just EqClass)) = "Eq "++ pp id ++ " =>" ++ pp id
  pp (IdType id (Just OrdClass)) = "Ord "++ pp id ++ " =>" ++ pp id
  -- Prints function types haskell style:
  -- pp (FunType arg ret) = ppClasses (FunType arg ret) ++ pp arg ++ " -> " ++ pp ret
  pp (FunType args ret) = 
    let types = getArgsTypes (FunType args ret) 
    in ppClasses (FunType args ret) ++ unwords (Prelude.map pp (init types)) ++ " -> " ++ pp (last types)
  pp (Void x) = "Void"

ppClasses :: SPLType -> String
ppClasses t = let c = Map.toList (getClasses t Map.empty) in if Prelude.null c then "" else unwords (Prelude.map printClass c) ++ "=>"
  where printClass (a, EqClass) = "Eq " ++ show a
        printClass (a, OrdClass) = "Ord " ++ show a

getClasses :: SPLType -> Map.Map IDLoc Class -> Map.Map IDLoc Class
getClasses (IdType id (Just EqClass)) map = 
  case Map.lookup id map of
    Just c -> map
    Nothing -> Map.insert id EqClass map
getClasses (IdType id (Just OrdClass)) map = Map.insert id OrdClass map
getClasses (TupleType (a,b) loc) map = getClasses a map `Map.union` getClasses b map
getClasses (ArrayType x loc) map = getClasses x map
getClasses (FunType args ret) map = getClasses args map `Map.union` getClasses ret map
getClasses x map = map

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
  pp (StmtFuncCall c _) = pp c ++ ";"
  pp (StmtReturn e _) = "return" ++ maybe "" ((" "++) . pp) e ++ ";"

instance PrettyPrinter Exp where
  pp (ExpId s f) = pp s ++ pp f
  pp (ExpInt i) = show i
  pp (ExpChar c) = show c
  pp (ExpBool b) = show b
  pp (ExpBracket e) = "("++ pp e++")"
  pp (ExpOp2 e1 op e2) = "("++ pp e1  ++" "++ pp op++" " ++ pp e2++")"
  pp (ExpOp1 op e) = pp op ++ pp e
  pp (ExpFunCall c) = pp c;
  pp (ExpList xs _) =  "["++ intercalate "," (Prelude.map pp xs)  ++ "]"
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