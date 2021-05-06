module AST where

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


data SPLType 
  = TypeBasic BasicType Loc
  | TupleType (SPLType, SPLType) Loc
  | ArrayType SPLType Loc
  | IdType IDLoc
  | FunType SPLType SPLType
  | Void Loc
  deriving (Eq, Show)

eqType :: SPLType -> SPLType -> Bool
eqType (TypeBasic l loc) (TypeBasic r loc') = l == r
eqType (TupleType (a,b) loc) (TupleType (c,d) loc') = eqType a c && eqType b d
eqType (ArrayType a loc) (ArrayType b loc') = eqType a b
eqType (IdType l) (IdType r) = True
eqType (FunType arg ret) (FunType arg' ret') = eqType arg arg' && eqType ret ret'
eqType (Void x) (Void x') = True
eqType _ _ = False


data BasicType
  = BasicInt
  | BasicBool
  | BasicChar
  deriving (Eq, Show)

data Stmt = StmtIf Exp [Stmt] (Maybe [Stmt]) Loc
          | StmtWhile Exp [Stmt] Loc 
          | StmtDeclareVar IDLoc Field Exp (Maybe SPLType)
          | StmtFuncCall FunCall Loc
          | StmtReturn (Maybe Exp) Loc
          deriving (Eq, Show)

data Exp
  = ExpId IDLoc Field
  | ExpInt Int Loc
  | ExpBool Bool Loc
  | ExpChar Char Loc
  | ExpBracket Exp
  | ExpOp2 Exp Op2Typed Exp Loc
  | ExpOp1 Op1 Exp Loc
  | ExpFunCall FunCall Loc
  | ExpEmptyList Loc
  | ExpList [Exp] Loc (Maybe SPLType)
  | ExpTuple (Exp, Exp) Loc (Maybe SPLType)
  deriving(Eq, Show)

newtype Field
  = Field [StandardFunction]
  deriving (Eq, Show)

data StandardFunction
    = Head Loc
    | Tail Loc
    | First Loc
    | Second Loc
    deriving (Eq, Show)

type ID = String
data IDLoc = ID String Loc
  deriving (Show, Eq)
instance Ord IDLoc where
  compare (ID id loc) (ID id' loc') = id `compare` id'

-- ===================== Loc ============================
data Loc = Loc Int Int
    deriving (Eq, Ord, Show)

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
  getLoc (IdType idloc) =  getLoc idloc
  getLoc (Void loc) = loc

  getLineNum (TypeBasic _ loc) = getLineNum loc
  getLineNum (ArrayType _ loc) = getLineNum loc
  getLineNum (TupleType _ loc) = getLineNum loc
  getLineNum (IdType idloc) = getLineNum idloc
  getLineNum (Void loc) = getLineNum loc

  getColNum (ArrayType _ loc) = getColNum loc
  getColNum (TupleType _ loc) = getColNum loc
  getColNum (TypeBasic _ loc) = getColNum loc
  getColNum (IdType idloc) = getColNum idloc
  getColNum (Void loc) = getColNum loc

instance LOC Exp where
  showLoc x = let Loc line col = getLoc x in "on Line " ++ show line ++ " and, Col "++ show col

  getLoc (ExpId idloc _) = getLoc idloc
  getLoc (ExpInt _ loc) =  loc
  getLoc (ExpBool _ loc) =  loc
  getLoc (ExpChar _ loc) =  loc
  getLoc (ExpBracket e) =  getLoc e
  getLoc (ExpOp2 _ _ _ loc) = loc
  getLoc (ExpOp1 _ _ loc) =   loc
  getLoc (ExpFunCall _ loc) = loc
  getLoc (ExpEmptyList loc) = loc
  getLoc (ExpList _ loc _) = loc
  getLoc (ExpTuple _ loc _) = loc

  getLineNum (ExpId idloc _) = getLineNum idloc
  getLineNum (ExpInt _ loc) =  getLineNum loc
  getLineNum (ExpBool _ loc) = getLineNum loc
  getLineNum (ExpChar _ loc) =  getLineNum loc
  getLineNum (ExpBracket e) =  getLineNum e
  getLineNum (ExpOp2 _ _ _ loc) = getLineNum loc
  getLineNum (ExpOp1 _ _ loc) =  getLineNum loc
  getLineNum (ExpFunCall _ loc) = getLineNum loc
  getLineNum (ExpEmptyList loc) = getLineNum loc
  getLineNum (ExpList _ loc _) = getLineNum loc
  getLineNum (ExpTuple _ loc _) = getLineNum loc

  getColNum (ExpId idloc _) = getColNum idloc
  getColNum (ExpInt _ loc) =  getColNum loc
  getColNum (ExpBool _ loc) =  getColNum loc
  getColNum (ExpChar _ loc) =  getColNum loc
  getColNum (ExpBracket e) =  getColNum e
  getColNum (ExpOp2 _ _ _ loc) = getColNum loc
  getColNum (ExpOp1 _ _ loc) =   getColNum loc
  getColNum (ExpFunCall _ loc) = getColNum loc
  getColNum (ExpEmptyList loc) = getColNum loc
  getColNum (ExpList _ loc _) = getColNum loc
  getColNum (ExpTuple _ loc _) = getColNum loc

-- ===================== FunCall and Operators ============================

data FunCall
    = FunCall IDLoc [Exp] (Maybe SPLType)
    deriving (Show, Eq)

-- ==== Op1 ====
data Op1 = Neg | Not deriving (Eq, Show)


data Op2Typed = Op2 Op2 (Maybe SPLType)
  deriving (Show, Eq)

-- ==== Op2 ====
data Op2 = 
  Plus|Min|Mult|Div|Mod|
  
  Le|Ge|Leq|Geq|Eq|Neq|
  
  And|Or|
  
  Con
  deriving (Show, Eq)

-- ===================== prettyPrinter ============================
prettyPrinter :: PrettyPrinter a => [a] -> String
prettyPrinter [] = ""
prettyPrinter (x:xs) = concatMap (\x -> unlines $ Prelude.map ("    "++) (lines $ pp x)) (x:xs)

class PrettyPrinter a where
  pp :: a -> String

instance PrettyPrinter SPL where
  pp (SPL []) = ""
  pp (SPL ((VarMain x):(FuncMain y):xs)) = pp x ++ "\n\n" ++ pp (SPL (FuncMain y:xs))
  pp (SPL ((VarMain x):decls)) = pp x ++ "\n" ++ pp (SPL decls)
  pp (SPL ((FuncMain x):decls)) = pp x ++ "\n\n" ++ pp (SPL decls)
  pp (SPL ((MutRec x):decls)) = "//mutRec\n" ++ pp x ++ "\n\n" ++ pp (SPL decls)

instance PrettyPrinter Loc where
  pp (Loc ln col) = "Line " ++ show ln ++ ", Col "++ show col


instance PrettyPrinter a => PrettyPrinter [a] where
  pp xs = intercalate "\n" (Prelude.map pp xs)

instance PrettyPrinter Decl where
  pp (VarMain x) = pp x
  pp (FuncMain x) = pp x  
  pp (MutRec x) = prettyPrinter x

instance PrettyPrinter VarDecl where
  pp (VarDeclVar i e) = "var " ++ pp i ++ " = "++ pp e ++ ";"
  pp (VarDeclType t i e ) = pp t ++ " " ++ pp i ++ " = "++ pp e ++ ";"

instance PrettyPrinter FunDecl where
  pp (FunDecl fName fArgs fType fVard fStmts) = 
    pp fName ++ " (" ++ intercalate ", " (Prelude.map pp fArgs) ++ ") " ++ (case fType of 
                                                              Just x -> ":: "++ pp x
                                                              Nothing -> "") ++ " {\n"++ 
    prettyPrinter fVard ++ (if not (Prelude.null fVard) then "\n" else "") ++
    prettyPrinter fStmts ++ 
    "}"

instance PrettyPrinter SPLType where
  pp (TypeBasic x loc) = pp x
  pp (TupleType (a, b) loc) = "(" ++ pp a ++ ", "++pp b ++ ")"
  pp (ArrayType x loc) = "["++pp x++"]"
  pp (IdType id) = pp id
  -- Prints function types haskell style:
  -- pp (FunType arg ret) = pp arg ++ " -> " ++ pp ret
  pp (FunType arg ret) = let args = getArgsTypes (FunType arg ret) in concatMap (\x -> pp x ++ " "  ) (init args) ++ "-> " ++ pp (last args)
  pp (Void x) = "Void"


getArgsTypes :: SPLType -> [SPLType]
getArgsTypes (FunType args ret) = getArgsTypes args ++ getArgsTypes ret
getArgsTypes x = [x]


instance PrettyPrinter BasicType where
  pp BasicInt = "Int"
  pp BasicBool = "Bool"
  pp BasicChar = "Char"

instance PrettyPrinter Stmt where
  pp (StmtIf e ifS elseS loc) = 
    "if (" ++ pp e ++ ") {\n" ++ 
      prettyPrinter ifS ++"}" ++ 
      case elseS of
        Just x -> " else {\n" ++ 
          prettyPrinter x ++"}" 
        Nothing -> ""
  pp (StmtWhile e s _) = 
    "while (" ++ pp e ++ ") {\n" ++  prettyPrinter s ++"}"
  pp (StmtDeclareVar id f e _) = pp id ++ pp f ++ " = " ++ pp e ++ ";"
  pp (StmtFuncCall c _) = pp c ++ ";"
  pp (StmtReturn e _) = "return" ++ maybe "" ((" "++) . pp) e ++ ";"

instance PrettyPrinter Exp where
  pp (ExpId s f) = pp s ++ pp f
  pp (ExpInt i _) = show i
  pp (ExpChar c _) = show c
  pp (ExpBool b _) = show b
  pp (ExpBracket e) = "("++ pp e++")"
  pp (ExpOp2 e1 (Op2 op _) e2 _) = "("++ pp e1  ++" "++ pp op++" " ++ pp e2++")"
  pp (ExpOp1 op e _) = pp op ++ pp e
  pp (ExpFunCall c _) = pp c;
  pp (ExpList xs _ _) =  "["++ intercalate "," (Prelude.map pp xs)  ++ "]"
  pp (ExpTuple (a,b) _ _) =  "(" ++ pp a ++ ", " ++ pp b ++")"
  pp (ExpEmptyList _) = "[]"

instance PrettyPrinter Field where
  pp (Field xs) = concatMap pp xs

instance PrettyPrinter StandardFunction where
  pp (Head _) = ".hd"
  pp (Tail _) = ".tl"
  pp (First _) = ".fst"
  pp (Second _) = ".snd"

instance PrettyPrinter IDLoc where
  pp (ID id (Loc line col)) = id

instance PrettyPrinter FunCall where
  pp (FunCall i eS Nothing) = pp i ++ "("++ intercalate "," (Prelude.map pp eS) ++") /*:: Nothing*/"
  pp (FunCall i eS (Just fType)) = pp i ++ "("++ intercalate "," (Prelude.map pp eS) ++") /*:: "++ pp fType ++"*/"

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

  -- ==================== Sorting SPL ====================
filterMain :: [Decl] -> ([Decl], Maybe Decl)
filterMain [] = ([],Nothing)
filterMain (FuncMain (FunDecl (ID "main" loc) [] (Just fType) vDecls stmts):xs) = let(ys, main) = filterMain xs in (ys, Just (FuncMain(FunDecl (ID "main" loc) [] (Just fType) vDecls stmts)))
filterMain (x:xs) = let(ys, main) = filterMain xs in (x:ys, main)

sortSPL :: SPL -> ([Decl],[Decl], Maybe Decl)
sortSPL (SPL xs) = sortDecls (reverse xs)

sortDecls :: [Decl] -> ([Decl],[Decl], Maybe Decl)
sortDecls [] = ([],[], Nothing)
sortDecls (VarMain x:xs) = let (globals,funcs,main) = sortDecls xs in (VarMain x:globals,funcs,main)
sortDecls (FuncMain (FunDecl (ID "main" l) [] fType locals stmts):xs) = 
    let (globals,funcs,main) = sortDecls xs 
    in (globals,funcs,Just (FuncMain (FunDecl (ID "main" l) [] fType locals stmts)))
sortDecls (FuncMain x:xs) = let (globals,funcs,main) = sortDecls xs in (globals,FuncMain x:funcs,main)