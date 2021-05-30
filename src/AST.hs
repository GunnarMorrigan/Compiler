module AST where

import Data.Map as Map
import Data.List ( intercalate )

import Debug.Trace

newtype SPL =  SPL [Decl] 
    deriving (Show, Eq)


data Decl 
    = VarMain VarDecl
    | FuncMain FunDecl
    | MutRec [FunDecl]
        deriving (Eq, Show)

data VarDecl 
    = VarDeclVar IDLoc Exp
    | VarDeclType SPLType IDLoc Exp 
        deriving (Eq, Show)

data FunDecl = 
    FunDecl IDLoc [IDLoc] (Maybe SPLType) [VarDecl] [Stmt]
        deriving (Eq, Show)

data SPLType 
    = TypeBasic Loc BasicType Loc
    | TupleType Loc (SPLType, SPLType) Loc
    | ArrayType Loc SPLType Loc
    | IdType IDLoc
    | FunType SPLType SPLType
    | Void Loc Loc
    
    | BracketType SPLType
    deriving (Show)


instance Eq SPLType where
  (==) (TypeBasic _ l loc) (TypeBasic _ r loc') = l == r
  (==) (TupleType _ (a,b) loc) (TupleType _ (c,d) loc') = (==) a c && (==) b d
  (==) (ArrayType _ a loc) (ArrayType _ b loc') = (==) a b
  (==) (IdType (ID _ l _)) (IdType (ID _ r _)) = l == r
  (==) (FunType arg ret) (FunType arg' ret') = (==) arg arg' && (==) ret ret'
  (==) (Void _ _) (Void _ _) = True
  (==) _ _ = False


-- eqType :: SPLType -> SPLType -> Bool
-- eqType (TypeBasic _ l loc) (TypeBasic _ r loc') = l == r
-- eqType (TupleType _ (a,b) loc) (TupleType _ (c,d) loc') = eqType a c && eqType b d
-- eqType (ArrayType _ a loc) (ArrayType _ b loc') = eqType a b
-- eqType (IdType (ID _ l _)) (IdType (ID _ r _)) = l == r
-- eqType (FunType arg ret) (FunType arg' ret') = eqType arg arg' && eqType ret ret'
-- eqType (Void _ _) (Void _ _) = True
-- eqType _ _ = False

isFunctionType :: SPLType -> Bool
isFunctionType (FunType arg ret) = True 
isFunctionType _ = False


isVoidFun :: SPLType -> Bool
isVoidFun x = last (getArgsTypes x) == Void (Loc (-1) (-1)) (Loc (-1) (-1))

data BasicType
  = BasicInt
  | BasicBool
  | BasicChar
  deriving (Eq, Show)

data Stmt = StmtIf Exp [Stmt] (Maybe [Stmt]) Loc
          | StmtWhile Exp [Stmt] Loc 
          | StmtAssignVar IDLoc Field Exp (Maybe SPLType)
          | StmtFuncCall FunCall Loc
          | StmtReturn (Maybe Exp) Loc
          deriving (Eq, Show)

data Exp
  = ExpId IDLoc Field
  | ExpInt Loc Int Loc
  | ExpBool Loc Bool Loc
  | ExpChar Loc Char Loc
  | ExpBracket Exp
  | ExpOp2 Loc Exp Op2Typed Exp Loc
  | ExpOp1 Loc Op1 Exp Loc
  | ExpFunCall Loc FunCall Loc
  | ExpEmptyList Loc Loc
  | ExpList Loc [Exp] Loc (Maybe SPLType)
  | ExpTuple Loc (Exp, Exp) Loc (Maybe SPLType)

  | ExpCurry Loc FunCurry Loc
  | ExpFunction Loc IDLoc Loc (Maybe SPLType)
  deriving(Show)

instance Eq Exp where
  (==) (ExpId id1 x) (ExpId id2 y) = id1 == id2 && x==y 
  (==) (ExpInt _ i1 _) (ExpInt _ i2 _) = i1==i2 
  (==) (ExpBool _ b1 _) (ExpBool _ b2 _) = b1 == b2 
  (==) (ExpChar _ c1 _) (ExpChar _ c2 _) =  c1 == c2

  (==) (ExpBracket e1) (ExpBracket e2) = e1 == e2 
  (==) (ExpOp2 _ l1 op1 l2 _) (ExpOp2 _ r1 op2 r2 _) = l1 == r1 && l2 == r2 && op1 == op2 
  (==) (ExpOp1 _ op1 e1 _) (ExpOp1 _ op2 e2 _) = op1 == op2 && e1 == e2 
  (==) (ExpFunCall _ f1 _) (ExpFunCall _ f2 _) = f1 == f2
  (==) (ExpEmptyList _ _) (ExpEmptyList _ _) = True
  (==) (ExpList _ es1 _ t1) (ExpList _ es2 _ t2) = es1 == es2 && t1 == t2
  (==) (ExpTuple _ (l1, l2) _ t1) (ExpTuple _ (r1, r2) _ t2) = l1 == r1 && l2 == r2 && t1 == t2

  (==) (ExpFunction _ id1 _ t1) (ExpFunction _ id2 _ t2) = id1 == id2  && t2 == t1

data FunCall
    = FunCall IDLoc [Exp] (Maybe SPLType)
    deriving (Show, Eq)

data FunCurry
    = FunCurry IDLoc [Exp] SPLType
    deriving (Show, Eq)

newtype Field
  = Field [StandardFunction]
  deriving (Eq, Show)

data StandardFunction
    = Head Loc Loc
    | Tail Loc Loc
    | Fst Loc Loc
    | Snd Loc Loc
    deriving (Eq, Show)

type ID = String
data IDLoc = ID Loc String Loc
  deriving (Show)

instance Eq IDLoc where
  (==) (ID _ id _) (ID _ id' _) = id == id'
instance Ord IDLoc where
  compare (ID _ id _) (ID _ id' _) = id `compare` id'

-- =====================Operators ============================
-- ==== Op1 ====
data Op1 = Neg | Not deriving (Eq, Show)

-- ==== Op2 ====
data Op2Typed = Op2 Op2 (Maybe SPLType) Loc
  deriving (Show)

instance Ord Op2Typed where
  (compare) (Op2 op1 t1 _) (Op2 op2 t2 _) = 
    case op1 `compare` op2 of
      EQ -> if t1 == t2 then EQ else LT 
      x -> x

instance Eq Op2Typed where
  (==) (Op2 op1 t1 _) (Op2 op2 t2 _) = op1 == op2 && t1 == t2

data Op2 = 
  Plus|Min|Mult|Div|Mod|
  
  Le|Ge|Leq|Geq|Eq|Neq|
  
  And|Or|
  
  Con
  deriving (Show, Eq, Ord)


-- ===================== Loc ============================
data Loc = 
  Loc Int Int
  deriving (Ord, Show)

instance Eq Loc where
  (==) (Loc a b) (Loc c d) = a==c && b==d

data ErrorLoc =
  -- SLoc Loc Int |    -- Single Loc, used when length of object is known
  DLoc Loc Loc      -- Double Loc, used when length of object is not known
  deriving (Show, Ord, Eq)

class LOC a where
  showLoc :: a -> String
  getDLoc :: a -> ErrorLoc
  getFstLoc :: a -> Loc
  getSndLoc :: a -> Loc
  getLineNum:: a -> Int
  getColNum:: a -> Int

instance LOC ErrorLoc where
  showLoc (DLoc (Loc line col) _) = "on Line " ++ show line ++ " and, Col "++ show col
  getDLoc x = x
  getFstLoc (DLoc a _) = a
  getSndLoc (DLoc _ b) = b
  getLineNum (DLoc (Loc line col) _) = line
  getColNum (DLoc (Loc line col) _) = col


instance LOC Loc where
  showLoc (Loc line col) = "on Line " ++ show line ++ " and, Col "++ show col
  getDLoc x = DLoc x x
  getFstLoc x = x
  getSndLoc x = x
  getLineNum (Loc line col) = line
  getColNum (Loc line col) = col

instance LOC IDLoc where
  showLoc (ID loc id loc') = showLoc loc
  getDLoc (ID locA id locB) = DLoc locA locB
  getFstLoc x = let (DLoc a _) = getDLoc x in a
  getSndLoc x = let (DLoc _ b) = getDLoc x in b
  getLineNum (ID loc id _) = getLineNum loc 
  getColNum (ID loc id _) = getColNum loc 

showIDLoc :: IDLoc -> String
showIDLoc (ID (Loc line col)  id _) | line > 0 && col > 0 = id ++ " on Line " ++ show line ++ " and, Col "++ show col
showIDLoc (ID (Loc line col)  id _) = id

idLocCreator :: String -> IDLoc
idLocCreator s = ID (Loc (-1) (-1)) s (Loc (-1) (-1))

instance LOC SPLType where
  showLoc x = let DLoc loc _ = getDLoc x in showLoc loc

  getDLoc (TypeBasic locA  _ locB) = DLoc locA locB
  getDLoc (ArrayType locA  _ locB) =  DLoc locA locB
  getDLoc (TupleType locA  _ locB) =  DLoc locA locB
  getDLoc (FunType arg ret) = DLoc (getFstLoc arg) (getSndLoc ret)
  getDLoc (IdType idloc) =  getDLoc idloc
  getDLoc (Void locA locB) = DLoc locA locB

  getFstLoc x = let (DLoc a _) = getDLoc x in a
  getSndLoc x = let (DLoc _ b) = getDLoc x in b

  getLineNum (TypeBasic locA  _ locBc) = getLineNum locA
  getLineNum (ArrayType locA  _ locB) = getLineNum locA
  getLineNum (TupleType locA  _ locB) = getLineNum locA
  getLineNum (IdType idloc) = getLineNum idloc
  getLineNum (Void locA locB) = getLineNum locA
  getLineNum x = getLineNum (getDLoc x)

  getColNum (ArrayType locA  _ locB) = getColNum locA
  getColNum (TupleType locA  _ locB) = getColNum locA
  getColNum (TypeBasic locA  _ locB) = getColNum locA
  getColNum (IdType idloc) = getColNum idloc
  getColNum (Void locA locB) = getColNum locA
  getColNum x = getColNum (getDLoc x)

instance LOC Exp where
  showLoc x = let DLoc loc _ = getDLoc x in showLoc loc

  getDLoc (ExpId idloc _) = getDLoc idloc
  getDLoc (ExpInt locA  _ locB) = DLoc locA locB
  getDLoc (ExpBool locA _ locB) = DLoc locA locB
  getDLoc (ExpChar locA _ locB) = DLoc locA locB
  getDLoc (ExpBracket e) =  getDLoc e
  getDLoc (ExpOp2 locA _ _ _ locB) = DLoc locA locB
  getDLoc (ExpOp1 locA _ _ locB) = DLoc locA locB
  getDLoc (ExpFunCall locA _ locB) = DLoc locA locB
  getDLoc (ExpEmptyList locA locB) = DLoc locA locB
  getDLoc (ExpList locA _ locB _) = DLoc locA locB
  getDLoc (ExpTuple locA _ locB _) = DLoc locA locB
  getDLoc (ExpFunction locA _ locB _) = DLoc locA locB

  getFstLoc x = let (DLoc a _) = getDLoc x in a
  getSndLoc x = let (DLoc _ b) = getDLoc x in b

  getLineNum x = getLineNum $ getFstLoc x
  -- getLineNum (ExpId idloc _) = getLineNum idloc
  -- getLineNum (ExpInt locA _ locB) =  getLineNum locA
  -- getLineNum (ExpBool locA _ locB) = getLineNum locA
  -- getLineNum (ExpChar locA _ locB) =  getLineNum locA
  -- getLineNum (ExpBracket e) =  getLineNum e
  -- getLineNum (ExpOp2 locA _ _ _ locB) = getLineNum locA
  -- getLineNum (ExpOp1 locA _ _ locB) =  getLineNum locA
  -- getLineNum (ExpFunCall locA _ locB) = getLineNum locA
  -- getLineNum (ExpEmptyList  locA locB) = getLineNum locA
  -- getLineNum (ExpList locA _ locB _) = getLineNum locA
  -- getLineNum (ExpTuple locA _ locB _) = getLineNum locA

  getColNum x = getColNum $ getFstLoc x
  -- getColNum (ExpId idloc _) = getColNum idloc
  -- getColNum (ExpInt locA _ locB) =  getColNum locA
  -- getColNum (ExpBool locA _ locB) =  getColNum locA
  -- getColNum (ExpChar locA _ locB) =  getColNum locA
  -- getColNum (ExpBracket e) =  getColNum e
  -- getColNum (ExpOp2 locA _ _ _ locB) = getColNum locA
  -- getColNum (ExpOp1 locA _ _ locB) =   getColNum locA
  -- getColNum (ExpFunCall locA _ locB) = getColNum locA
  -- getColNum (ExpEmptyList locA locB) = getColNum locA
  -- getColNum (ExpList locA _ locB _) = getColNum locA
  -- getColNum (ExpTuple locA _ locB _) = getColNum locA

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
  pp (TypeBasic _ x loc) = pp x
  pp (TupleType _ (a, b) loc) = "(" ++ pp a ++ ", "++pp b ++ ")"
  pp (ArrayType _ x loc) = "["++pp x++"]"
  pp (IdType id) = pp id
  -- Prints function types haskell style:
  -- pp (FunType arg ret) = pp arg ++ " -> " ++ pp ret
  pp (FunType arg ret) = let args = getArgsTypes (FunType arg ret) in concatMap (\x -> ppFuncs x ++ " "  ) (init args) ++ "-> " ++ pp (last args)
    where ppFuncs x = if isFunctionType x then "("++ pp x ++")" else pp x
  pp (Void _ _) = "Void"

  pp (BracketType t) = "(" ++ pp t ++ ")"


getArgsTypes :: SPLType -> [SPLType]
getArgsTypes (FunType arg ret) = arg:getArgsTypes ret
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
  pp (StmtAssignVar id f e _) = pp id ++ pp f ++ " = " ++ pp e ++ ";"
  pp (StmtFuncCall c _) = pp c ++ ";"
  pp (StmtReturn e _) = "return" ++ maybe "" ((" "++) . pp) e ++ ";"

instance PrettyPrinter Exp where
  pp (ExpId s f) = pp s ++ pp f
  pp (ExpInt _ i _) = show i
  pp (ExpChar _ c _) = show c
  pp (ExpBool _ b _) = show b
  pp (ExpBracket e) = "("++ pp e++")"
  pp (ExpOp2 _ e1 (Op2 op _ _) e2 _) = "("++ pp e1  ++" "++ pp op++" " ++ pp e2++")"
  pp (ExpOp1 _ op e _) = pp op ++ pp e
  pp (ExpFunCall _ c _) = pp c;
  pp (ExpList _ xs _ _) =  "["++ intercalate "," (Prelude.map pp xs)  ++ "]"
  pp (ExpTuple _ (a,b) _ _) =  "(" ++ pp a ++ ", " ++ pp b ++")"
  pp (ExpEmptyList _ _) = "[]"
  pp (ExpFunction _ id _ (Just t)) = pp id {-- ++ " :: " ++ pp t --}

instance PrettyPrinter Field where
  pp (Field xs) = concatMap pp xs

instance PrettyPrinter StandardFunction where
  pp (Head _ _) = ".hd"
  pp (Tail _ _) = ".tl"
  pp (Fst _ _) = ".fst"
  pp (Snd _ _) = ".snd"

instance PrettyPrinter IDLoc where
  pp (ID _ id _) = id

instance PrettyPrinter FunCall where
  pp (FunCall i eS Nothing) = pp i ++ "("++ intercalate ", " (Prelude.map pp eS) ++") /*:: Nothing*/"
  pp (FunCall i eS (Just fType)) = pp i ++ "("++ intercalate ", " (Prelude.map pp eS) ++") /*:: "++ pp fType ++"*/"

instance PrettyPrinter Op1 where
  pp Neg = "-"
  pp Not = "!"
instance PrettyPrinter Op2Typed where
  pp (Op2 op (Just t) loc) = show op ++ " :: " ++ pp t

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
filterMain (FuncMain (FunDecl (ID locA "main" locB) [] (Just fType) vDecls stmts):xs) = let(ys, main) = filterMain xs in (ys, Just (FuncMain(FunDecl (ID locA "main" locB) [] (Just fType) vDecls stmts)))
filterMain (x:xs) = let(ys, main) = filterMain xs in (x:ys, main)

sortSPL :: SPL -> ([VarDecl],[FunDecl], Maybe FunDecl)
sortSPL (SPL xs) = sortDecls (reverse xs)

sortDecls :: [Decl] -> ([VarDecl],[FunDecl], Maybe FunDecl)
sortDecls [] = ([],[], Nothing)
sortDecls (VarMain x:xs) = let (globals,funcs,main) = sortDecls xs in (x:globals,funcs,main)
sortDecls (FuncMain (FunDecl (ID locA "main" locB) [] fType locals stmts):xs) = 
    let (globals,funcs,main) = sortDecls xs 
    in (globals,funcs,Just (FunDecl (ID locA "main" locB) [] fType locals stmts))
sortDecls (FuncMain x:xs) = let (globals,funcs,main) = sortDecls xs in (globals,x:funcs,main)