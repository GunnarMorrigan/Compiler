module Gen where

import AST
import Error
import Parser
import MutRec
import TI

import Data.Char
import Data.List ( intercalate )
import Data.Map as Map
import Data.Bifunctor as BI

data Mem =
    H Int |
    L Int
    deriving (Show, Eq)

data Scope = Global | Local

class GenCode a where
    gen :: a -> [String] -> GenEnv -> [String]

type GenEnv = Map IDLoc Mem

instance GenCode a => GenCode [a] where
    gen [] c env = c
    gen (x:xs) c env = gen x (gen xs c env) env

instance GenCode SPL where
    gen (SPL decls) c env = "bra main":gen decls c env

instance GenCode Decl where
    gen (VarMain varDecl) c = genVarDecl varDecl c Global
    gen (FuncMain funDecl) c = gen funDecl c

genVarDecls :: [VarDecl] -> [String] -> Scope -> Map IDLoc Mem -> [String]
genVarDecls [] c _ _ = c
genVarDecls (x:xs) c s env = genVarDecl x (genVarDecls xs c s env) s env

-- instance GenCode VarDecl where
genVarDecl :: VarDecl -> [String] -> Scope -> Map IDLoc Mem -> [String]
genVarDecl (VarDeclType t i e) c Global env = case Map.lookup i env of
    Just h -> gen e (sth h:c) env
    Nothing -> error ("Variable " ++ show i ++ " unkown in generator " ++ showLoc i)
genVarDecl (VarDeclType t i e) c Local env = case Map.lookup i env of
    Just l -> gen e (stl l:c) env
    Nothing -> error ("Variable " ++ show i ++ " unkown in generator " ++ showLoc i)
genVarDecl (VarDeclVar _ _) c _ env = undefined

instance GenCode FunDecl where
    gen (FunDecl (ID "main" _) [] (Just fType) vDecls stmts) c env = do
        let env' = constructEnv env [] vDecls 
        case length vDecls of
            0 -> let x = gen stmts (["trap 0","halt","; THE END debug:"] ++ c) env' in
                ("main : "++ head x) : tail x
            l -> ("main : link " ++ show l): genVarDecls vDecls (gen stmts (["trap 0","halt","; THE END debug:"] ++ c) env') Local env'
    gen (FunDecl (ID name _) args (Just fType) vDecls stmts) c env = do
        let env' = constructEnv env args vDecls
        case length vDecls of
            0 -> (name ++ ": link 0"): gen stmts c env'
            l -> (name ++ ": link " ++ show l): genVarDecls vDecls (gen stmts c env') Local env'

instance GenCode Stmt where
    gen (StmtIf e stmts els loc) c env = undefined
    gen (StmtWhile e stmts loc) c env = undefined
    gen (StmtDeclareVar (ID name loc) field exp) c env = undefined
    -- MAKE USE OF THE fType in funCall for overloading
    gen (StmtFuncCall (FunCall id args Nothing) loc) c env = undefined
    gen (StmtFuncCall (FunCall id args (Just fType)) loc) c env = do
        let c' = if isVoidFun fType then c else "ldr RR":c
        let c'' = (if Prelude.null args then c' else ajs (negate $ length args):c')
        gen args (("bsr " ++ pp id):c'') env
    gen (StmtReturn exp loc) c env =  case exp of
        Nothing -> "unlink":"ret":c
        Just e -> gen e ("str RR":"unlink":"ret": c) env

isVoidFun :: SPLType -> Bool
isVoidFun x = last (getArgsTypes x) `eqType` Void defaultLoc

constructEnv :: GenEnv -> [IDLoc] -> [VarDecl] -> GenEnv
constructEnv env xs ys = fromList (Prelude.map (BI.second L) (args ++ zip decls [1..])) `union` env
    where
        args = zip xs [(negate (length xs)-1 )..]
        decls = Prelude.map (\(VarDeclType t id e) -> id) ys

-- genExp :: Exp -> [String] -> Map IDLoc Int -> [String]

instance GenCode Exp where
    gen (ExpId id field) c env = case Map.lookup id env of
        Just (L x) -> ldl x : c
        Just (H x) -> ldh x : c
        Nothing -> error ("Variable " ++ show id ++ " unkown in generator " ++ showLoc id)
    gen (ExpInt i _) c env = ldc i:c
    gen (ExpBool b loc) c env= ldc (if b then -1 else 0  ):c
    gen (ExpChar char loc) c env = ldc (ord char):c
    gen (ExpBracket e) c env = gen e c env
    gen (ExpOp2 e1 op e2 loc) c env  = gen e1 (gen e2 (gen op c env) env) env
    gen (ExpOp1 op e loc) c env = case op of
            Neg -> gen e ("neg":c) env
            Not -> gen e ("not":c) env

instance GenCode Op2Typed where
    gen (Op2 Plus _) c _ = "add":c
    gen (Op2 Min _) c _ = "sub":c
    gen (Op2 Mult _) c _= "mul":c
    gen (Op2 Div _) c _= "div":c
    gen (Op2 Mod _) c _= "mod":c
    -- Should be extended for other types of comparison
    gen (Op2 Le (Just opType)) c _= "lt":c
    gen (Op2 Ge (Just opType)) c _= "gt":c
    gen (Op2 Leq (Just opType)) c _= "le":c
    gen (Op2 Geq (Just opType)) c _= "ge":c
    gen (Op2 Eq (Just opType)) c _= "eq":c
    gen (Op2 Neq (Just opType)) c _= "ne":c

    gen (Op2 And _) c _= "and":c
    gen (Op2 Or _) c _= "or":c

    gen (Op2 Con (Just opType)) c _= undefined

-- Load Local. Pushes a value relative to the markpointer.
ldl :: Int -> String
ldl x = "ldl " ++ show x

stl :: Mem -> String
stl (L x) = "stl " ++ show x

-- Load Constant. Pushes the inline constant on the stack.
ldc :: Int -> String
ldc x = "ldc " ++ show x

-- Adjust Stack. Adjusts the stackpointer with fixed amount.
ajs :: Int -> String
ajs x = "ajs " ++ show x

-- Load from Heap. Pushes a value pointed to by the value at the top of the stack. The pointer value is offset by a constant offset.
ldh :: Int -> String
ldh x = "ldl " ++ show x

sth :: Mem -> String 
sth (H x) = "sth " ++ show x


mainGen filename = do
      file <- readFile  ("../SPL_test_code/" ++ filename)
      case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
            Right(_, _, spl) -> do
                let output = intercalate "\n" $ gen spl ["\n"] empty
                writeFile "../generated_ssm/gen.ssm" output
            Left x -> putStr $ show x ++ "\n" ++ showPlaceOfError file x