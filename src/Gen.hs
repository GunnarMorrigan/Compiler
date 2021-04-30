{-# LANGUAGE TypeSynonymInstances #-}
module Gen where

import AST
import Error
import Parser
import MutRec
import TI

import Data.Char
import Data.List ( intercalate )
import Data.Map as Map
import Data.Either
import Data.Bifunctor as BI
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import Control.Applicative

-- ===== Types ====

data Mem =
    G Int |
    H Int |
    L Int
    deriving (Show, Eq)

data Scope = Global | Local

type GenState = Int
type Gen a = ExceptT Error (State GenState) a
 
type GenEnv = Map IDLoc Mem

class GenCode a where
    gen :: a -> [String] -> GenEnv -> Gen [String]

runGen :: Gen a -> (Either Error a, GenState)
runGen t = runState (runExceptT t) initState
  where initState = 0

-- ===== Generation =====

instance GenCode a => GenCode [a] where
    gen [] c env = return c
    gen (x:xs) c env = do
        c' <- gen xs c env
        gen x c' env

instance GenCode SPL where
    gen (SPL decls) c env = do
        c' <- gen decls c env
        return $ "bra main":c'

instance GenCode Decl where
    gen (VarMain varDecl) c = genVarDecl varDecl c Global
    gen (FuncMain funDecl) c = gen funDecl c

genVarDecls :: [VarDecl] -> [String] -> Scope -> GenEnv -> Gen [String]
genVarDecls [] c _ _ = return c
genVarDecls (x:xs) c s env = do
    c' <- genVarDecls xs c s env
    genVarDecl x c' s env

-- instance GenCode VarDecl where
genVarDecl :: VarDecl -> [String] -> Scope -> GenEnv -> Gen [String]
genVarDecl (VarDeclType t i e) c Global env = case Map.lookup i env of
    Just h -> gen e (sth h:c) env
    Nothing -> error ("Variable " ++ show i ++ " unkown in generator " ++ showLoc i)
genVarDecl (VarDeclType t i e) c Local env = case Map.lookup i env of
    Just l -> gen e (stl l:c) env
    Nothing -> error ("Variable " ++ show i ++ " unkown in generator " ++ showLoc i)
genVarDecl (VarDeclVar _ _) c _ env = undefined

newIf :: String -> Gen (String, String)
newIf name = do  
    s <- get
    put (s + 1)
    return (name++"_ifTh"++show s++":    ",name++"_ifCon"++show s++":    ")

instance GenCode FunDecl where
    gen (FunDecl (ID "main" loc) [] (Just fType) vDecls stmts) c env = do
        put 0
        let env' = constructEnv env [] vDecls 
        c' <- genStmts stmts (["trap 0","halt","; THE END debug:"] ++ c) (ID "main" loc) env'
        c'' <- genVarDecls vDecls c' Local env'
        return $ ("main : link " ++ show (length vDecls)):c''

    gen (FunDecl (ID name loc) args (Just fType) vDecls stmts) c env = do
        put 0

        let env' = constructEnv env args vDecls
        c' <- genStmts stmts c (ID name loc) env'
        c'' <- genVarDecls vDecls c' Local env'

        return $ (name ++ ": link " ++ show (length vDecls)):c''

genReturn :: SPLType -> [String]
genReturn f = undefined 

genStmts :: [Stmt] -> [String] -> IDLoc -> GenEnv -> Gen [String]
genStmts [] c id env = return c
-- The following two are here and not in genStmt because here we know if we need a continuation for something after the if stmt.
genStmts ((StmtIf e stmts Nothing loc):xs) c (ID name l) env = do
    (th, contin) <- newIf name
    
    c' <- genStmts stmts c (ID name l) env
    continC <- genStmts xs c' (ID name l) env
    let c'' = brt th:continC
    gen e c'' env

genStmts ((StmtIf e stmts (Just els) loc):xs) c (ID name l) env = do
    (th, contin) <- newIf name

    continC <- (if Prelude.null xs then return c else insertLabel contin <$> genStmts xs c (ID name l) env)
    c' <- genStmts stmts continC (ID name l) env
    let thC = insertLabel th c'
    elseC <- genStmts els thC (ID name l) env
    let conditionC = brt th:elseC
    
    gen e conditionC env

genStmts (x:xs) c id env = do
    c' <- genStmts xs c id env 
    genStmt x c' id env

genStmt :: Stmt -> [String] -> IDLoc -> GenEnv -> Gen [String]

genStmt (StmtIf e stmts (Just els) loc) c (ID name l) env = do
    (th, contin) <- newIf name

    let continC = insertLabel contin c
    c' <- genStmts stmts continC (ID name l) env
    let thC = insertLabel th c'
    elseC <- genStmts els thC (ID name l) env
    let conditionC = brt th:elseC
    
    gen e conditionC env
genStmt (StmtWhile e stmts loc) c id env = undefined
genStmt (StmtDeclareVar (ID name loc) field exp) c _ env = undefined
genStmt (StmtFuncCall (FunCall id args Nothing) loc) c _ env = undefined
-- MAKE USE OF THE fType in funCall for overloading
genStmt (StmtFuncCall (FunCall id args (Just fType)) loc) c _ env = do
    let c' = if isVoidFun fType then c else "ldr RR":c
    let c'' = (if Prelude.null args then c' else ajs (negate $ length args):c')
    gen args (("bsr " ++ pp id):c'') env
genStmt (StmtReturn exp loc) c (ID id _) env =
    let retLink = "bra " ++ id ++ "End" in case exp of
    Nothing -> return $ retLink:c --"unlink":"ret":c
    Just e -> gen e (retLink:c) env --("str RR":"unlink":"ret": c) env

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
        Just (L x) -> return $ ldl x : c
        Just (G x) -> return $ ldh (G x) : c
        Nothing -> error ("Variable " ++ show id ++ " unkown in generator " ++ showLoc id)
    gen (ExpInt i _) c env = return $ ldc i:c
    gen (ExpBool b loc) c env= return $ ldc (if b then -1 else 0  ):c
    gen (ExpChar char loc) c env = return $ ldc (ord char):c
    gen (ExpBracket e) c env = gen e c env
    
    gen (ExpOp2 e1 op e2 loc) c env  = do
        c' <- gen op c env
        c'' <- gen e2 c' env
        gen e1 c'' env
    gen (ExpOp1 op e loc) c env = case op of
            Neg -> gen e ("neg":c) env
            Not -> gen e ("not":c) env

instance GenCode Op2Typed where
    gen (Op2 Plus _) c _ = return $ "add":c
    gen (Op2 Min _) c _ = return $ "sub":c
    gen (Op2 Mult _) c _= return $ "mul":c
    gen (Op2 Div _) c _= return $ "div":c
    gen (Op2 Mod _) c _= return $ "mod":c
    -- Should be extended for other types of comparison
    gen (Op2 Le (Just opType)) c _= return $ "lt":c
    gen (Op2 Ge (Just opType)) c _= return $ "gt":c
    gen (Op2 Leq (Just opType)) c _= return $ "le":c
    gen (Op2 Geq (Just opType)) c _= return $ "ge":c
    gen (Op2 Eq (Just opType)) c _= return $ "eq":c
    gen (Op2 Neq (Just opType)) c _= return $ "ne":c

    gen (Op2 And _) c _= return $ "and":c
    gen (Op2 Or _) c _= return $ "or":c

    gen (Op2 Con (Just opType)) c _= undefined


insertLabel :: String -> [String] -> [String]
insertLabel label (x:xs) = (label++x):xs


-- ===== Local =====

-- Load Local. Pushes a value relative to the markpointer.
ldl :: Int -> String
ldl x = "ldl " ++ show x

stl :: Mem -> String
stl (L x) = "stl " ++ show x


-- ===== Branching =====

-- Branch on True. If a True value is on top of the stack, jump to the destination.
brt :: String -> String 
brt name = "brt "++name

-- Branch on False. If a False value is on top of the stack, jump to the destination.
brf :: String -> String 
brf name = "brf "++name

-- Branch Allways. Jumps to the destination. Replaces the PC with the destination address.
bra :: String -> String 
bra name = "bra "++name

-- ===== Abitrary =====

-- Load Constant. Pushes the inline constant on the stack.
ldc :: Int -> String
ldc x = "ldc " ++ show x

-- Adjust Stack. Adjusts the stackpointer with fixed amount.
ajs :: Int -> String
ajs x = "ajs " ++ show x


-- ===== Heap =====

-- Load from Heap. Pushes a value pointed to by the value at the top of the stack. The pointer value is offset by a constant offset.
ldh :: Mem -> String
ldh (H x) = "ldl " ++ show x

-- Store into Heap. Pops 1 value from the stack and stores it into the heap. Pushes the heap address of that value on the stack.
sth :: Mem -> String 
sth (H x) = "sth " ++ show x


mainGen :: String -> IO ()
mainGen filename = do
      file <- readFile  ("../SPL_test_code/" ++ filename)
      case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
            Right(_, _, spl) -> do
                let res = runGen (gen spl ["\n"] Map.empty)
                let (Right result,_) = res
                let output = intercalate "\n" result
                writeFile "../generated_ssm/gen.ssm" output
            Left x -> putStr $ "ERROR:\n" ++ show x ++ "\n" ++ showPlaceOfError file x