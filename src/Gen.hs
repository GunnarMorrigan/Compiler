{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
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

import Debug.Trace

-- ===== Types ====

data Mem =
    G Int SPLType |
    L Int SPLType |
    H Int SPLType |
    R5 
    deriving (Show, Eq)

data Scope = Global | Local

type GenState = (Int,Int)
type Gen a = ExceptT Error (State GenState) a
 
type GenEnv = Map IDLoc Mem

runGen :: Gen a -> (Either Error a, GenState)
runGen t = runState (runExceptT t) initState
  where initState = (0,0)

-- ===== State manipulation =====
resetIf :: Gen ()
resetIf = do
    (ifS,globalS) <- get
    put (0,globalS)

newIf :: String -> Gen (String, String)
newIf name = do  
    (ifS,globalS) <- get
    put (ifS + 1,globalS)
    return (name++"_ifTh"++show ifS,name++"_ifCon"++show ifS)

newGlobal :: SPLType -> Gen Mem
newGlobal typ = do
    (ifS,globalS) <- get
    put (ifS,globalS + 1)
    return $ G globalS typ

-- ===== Generation =====
class GenCode a where
    gen :: a -> [String] -> GenEnv -> Gen ([String], GenEnv)

instance GenCode a => GenCode [a] where
    gen [] c env = return (c, env)
    gen (x:xs) c env = do
        combineResult (gen x [] env) (gen xs c)

instance GenCode SPL where
    gen spl c env =
        let (globals, functions) = sortSPL spl in trace ("SPL globals \n\n" ++ show globals) $ do
        combineResult (genGlobals globals [] env) (gen functions c)

instance GenCode Decl where
    gen (VarMain varDecl) c = genVarDecl varDecl c Global
    gen (FuncMain funDecl) c = gen funDecl c

genGlobals :: [Decl] -> [String] -> GenEnv -> Gen ([String], GenEnv)
genGlobals globals c env = do
    (res, env') <- gen globals ("bra main":c) env
    return ("ldsa 1":store R5:res, env')

genVarDecls :: [VarDecl] -> [String] -> Scope -> GenEnv -> Gen ([String], GenEnv)
genVarDecls [] c _ env = return (c, env)
genVarDecls (x:xs) c s env = do
    combineResult (genVarDecl x [] s env) (genVarDecls xs c s)

genVarDecl :: VarDecl -> [String] -> Scope -> GenEnv -> Gen ([String], GenEnv)
genVarDecl (VarDeclType t id e) c Global env = trace ("GLOBAL varDecl "++ show id ++ show env) $ do
    mem <- newGlobal t
    let env' = Map.insert id mem env
    gen e c env'
    -- UPDATE ENV HIER, dit is een error zodat ik weet dat dit nog moet.
genVarDecl (VarDeclType t i e) c Local env = case Map.lookup i env of
    Just memLoc -> gen e (store memLoc:c) env
    Nothing -> error ("Variable " ++ show i ++ " unkown in generator " ++ showLoc i)
genVarDecl (VarDeclVar _ _) c _ env = undefined

instance GenCode FunDecl where
    gen (FunDecl (ID "main" loc) [] (Just fType) vDecls stmts) c env = do
        resetIf
        let env' = constructEnv env fType [] vDecls
        
        (res,env'') <- combineResult (genVarDecls vDecls [] Local env') (genStmts stmts ("trap 0":"halt":c) (ID "main" loc))

        return (insertLabel "main" (("link " ++ show (length vDecls)):res),env'')

    gen (FunDecl (ID name loc) args (Just fType) vDecls stmts) c env = do
        resetIf
        let env' = constructEnv env fType args vDecls
        
        (res,env'') <- combineResult
                            (genVarDecls vDecls [] Local env')
                            (genStmts stmts (genReturn fType name c) (ID name loc))
        
        return (insertLabel name (("link " ++ show (length vDecls)):res),env'')

    gen (FunDecl (ID "main" loc) _ _ _ _) _ _ = 
        throwError $ Error (getLineNum loc) (getColNum loc) "main function can't have arguments, return objects etc."

genReturn :: SPLType -> String -> [String] -> [String]
genReturn fType fName c | isVoidFun fType = (fName++"End:    unlink"):"    ret": c
genReturn fType fName c = (fName++"End:  str RR"):"    unlink":"    ret": c

genStmts :: [Stmt] -> [String] -> IDLoc -> GenEnv -> Gen ([String], GenEnv)
genStmts [] c id env = return (c, env)
-- The following two are here and not in genStmt because here we know if we need a continuation for something after the if stmt.
genStmts ((StmtIf e stmts Nothing loc):xs) c (ID name l) env = do
    (th, contin) <- newIf name

    (ifStmt, env') <- combineResult (gen e [brf contin] env) (genStmts stmts [] (ID name l))
    
    (rest, env'') <- BI.first (insertLabel contin) <$> genStmts xs c (ID name l) env'

    return $ if Prelude.null xs 
            then (ifStmt, env')
            else (ifStmt ++ rest, env'')
 
genStmts ((StmtIf e stmts (Just els) loc):xs) c (ID name l) env = do
    (th, contin) <- newIf name

    (elseStmt, env') <- combineResult (gen e [brt th] env) (genStmts els [bra contin] (ID name l))

    (ifElseStmt, env'') <- BI.first (insertLabel th) <$> genStmts stmts [] (ID name l) env'

    (rest, env''') <- BI.first (insertLabel contin) <$> genStmts xs c (ID name l) env''

    return $ if Prelude.null xs 
                then (elseStmt++ifElseStmt++c, env'') 
                else (elseStmt++ifElseStmt++rest, env''') 
genStmts [StmtReturn exp loc] c id env =
    case exp of
        Nothing -> return (c, env)
        Just e -> gen e c env
genStmts (x:xs) c id env = do
    combineResult (genStmt x [] id env) (genStmts xs c id) 

genStmt :: Stmt -> [String] -> IDLoc -> GenEnv -> Gen ([String], GenEnv)
genStmt (StmtWhile e stmts loc) c id env = undefined
genStmt (StmtDeclareVar (ID name loc) field exp) c _ env = undefined
genStmt (StmtFuncCall funcall _) c _ env = 
    genFuncCall funcall c env
genStmt (StmtReturn exp loc) c (ID id _) env =
    let retLink = "bra " ++ id ++ "End" in case exp of
    Nothing -> return (retLink:c, env) --"unlink":"ret":c
    Just e -> gen e (retLink:c) env
genStmt stmt c _ env = throwError $ Error (-1) (-1) ("Failed to catch the following object:\n" ++ show stmt)

-- MAKE USE OF THE fType in funCall for overloading
genFuncCall :: FunCall -> [String] -> GenEnv -> Gen ([String], GenEnv)
genFuncCall (FunCall (ID "print" _) args (Just fType)) c env = undefined 
genFuncCall (FunCall (ID "isEmpty" _) args (Just fType)) c env = undefined 
genFuncCall (FunCall id args (Just fType)) c env = do
    let c' = if isVoidFun fType then c else "ldr RR":c
    let c'' = (if Prelude.null args then c' else ajs (negate $ length args):c')
    gen args (("bsr " ++ pp id):c'') env


instance GenCode Exp where
    gen (ExpId id field) c env = case Map.lookup id env of
        Just mem -> return (load mem ++ c, env )
        Nothing -> error ("Variable " ++ show id ++ " unkown in generator " ++ showLoc id)
    gen (ExpInt i _) c env = return (ldc i:c, env)
    gen (ExpBool b _) c env= return ( ldc (if b then -1 else 0  ):c, env)
    gen (ExpChar char _) c env = return (ldc (ord char):c, env)
    gen (ExpBracket e) c env = gen e c env
    
    gen (ExpEmptyList _) c env = return ("":c, env)

    gen (ExpTuple (e1, e2) loc (Just (TupleType (t1,t2) _))) c env = do
        let storeTuple = "stmh 2":c
        combineResult (gen e1 [] env) (gen e2 storeTuple)
    
    gen (ExpFunCall funcall _) c env =
        genFuncCall funcall c env

    gen (ExpOp2 e1 op e2 loc) c env  = do
        let args = combineResult (gen e1 [] env) (gen e2 [])
        combineResult args (gen op ("ldr RR":c))
    gen (ExpOp1 op e loc) c env = case op of
        Neg -> gen e ("neg":c) env
        Not -> gen e ("not":c) env

instance GenCode Op2Typed where
    gen (Op2 Plus _) c env = return ("add":c,env)
    gen (Op2 Min _) c env = return ("sub":c,env)
    gen (Op2 Mult _) c env = return ("mul":c,env)
    gen (Op2 Div _) c env = return ("div":c,env)
    gen (Op2 Mod _) c env = return ("mod":c,env)

    gen (Op2 And _) c env = return ("and":c,env)
    gen (Op2 Or _) c env = return ("or":c,env)

    gen (Op2 Con (Just opType)) c env = undefined

    -- Should be extended for other types of comparison
    gen (Op2 op (Just (FunType t _))) c env = do
        (func, c', env') <- genCompare op t c env
        return (bsr func:c', env')


genCompare :: Op2 -> SPLType -> [String] -> GenEnv -> Gen (String, [String], GenEnv)
genCompare op (TypeBasic _ _) c env = return (op2Func op,c,env)
genCompare op (TupleType (a,b) _) c env = do
    let fName = op2Func op ++ "Tuple"
    let check = brf (fName++"End")

    let start = fName++":  link 0"

    (bBSRfName, bC, env')  <- genCompare op b [] env
    (aBSRfName, aC, env'') <- genCompare op a bC env'

    let endBranch = (fName++"End:  str RR"):"    unlink":"    ajs -2":"    ret": c
    let compareB = ["ldl -3","ldc 1","add","ldl -2","ldc 1","add",bBSRfName]
    let compare = "ldl -3":"ldh 0":"ldl -2":"ldh 0":aBSRfName:"str R6":"ldr R6":"ldr R6": check:compareB

    return (fName, c ++start:compare++endBranch++aC ,env'')


-- genOverloadedCompare op level fName (ArrayType a _ ) c env = undefined
-- genOverloadedCompare :: Op2 -> Int -> String -> SPLType -> [String] -> GenEnv -> Gen ([String], GenEnv)
-- genOverloadedCompare op level fName (TypeBasic _ _) c env = return (op2Func op:c,env)
-- genOverloadedCompare op level fName (TupleType (a,b) _) c env = do
--     let branch = if level == 0 then c else brf (fName++"End"):c
--     combineResult
--         (genOverloadedCompare op (level+1) fName a [brf (fName++"End")] env)
--         (genOverloadedCompare op (level+1) fName b branch)
-- genOverloadedCompare op level fName (ArrayType a _ ) c env = undefined

-- genOverloadedFunction :: Op2 -> SPLType -> [String] -> GenEnv -> Gen ([String], GenEnv)
-- genOverloadedFunction op (TypeBasic _ _) c env = return (op2Func op:c,env)
-- genOverloadedFunction op opType c env = do
--     let (FunType argType _) = opType 
--     let fName = op2Func op ++ typeToName argType
--     (functionBody, env') <- genOverloadedCompare 
--                                 op 0
--                                 fName
--                                 argType [] env
--     let returnBody = genReturn opType fName c
--     return ((fName ++ ":  link 0"):functionBody ++ returnBody, env')


typeToName :: SPLType -> String 
typeToName (TypeBasic x _) = pp x
typeToName (TupleType (t1,t2) _) = "Tuple"
typeToName (ArrayType a1 _) = "Array"
typeToName (FunType arg f) = "Func"
typeToName (Void _) = "Void"

op2Func :: Op2 -> String
op2Func Le  = "lt"
op2Func Ge  = "gt"
op2Func Leq = "le"
op2Func Geq = "ge"
op2Func Eq  = "eq"
op2Func Neq = "ne"

-- ==================== Helper functions ====================

combineResult :: Gen ([String], GenEnv) -> (GenEnv -> Gen ([String], GenEnv)) -> Gen ([String], GenEnv)
combineResult a b = do
    (resA, env) <- a
    BI.first (resA++) <$> b env 

insertLabel :: String -> [String] -> [String]
insertLabel label (x:xs) = (label++":  "++x):xs

isVoidFun :: SPLType -> Bool
isVoidFun x = last (getArgsTypes x) `eqType` Void defaultLoc

-- globalsRegister :: String
-- globalsRegister = "R5"

-- ==================== Environment ====================
constructEnv :: GenEnv -> SPLType -> [IDLoc] -> [VarDecl] -> GenEnv
constructEnv env fType xs ys = fromList decls `union` fromList args `union` env
    where
        args = zipWith3 (\ id loc typ -> (id, L loc typ)) xs [(negate (length xs)-1 )..] (init $ getArgsTypes fType)
        decls = zipWith (\(VarDeclType t id e) b -> (id, L b t) ) ys [1..]

-- ==================== Instructions ====================
load :: Mem -> [String] 
load (L x _) = ["ldl " ++ show x]
load (H x _) = undefined
load (G x _) = case x of
    0 -> load R5++["lda 0"]
    _ -> load R5++["ldc " ++ show x, "add", "lda 0"]
load R5      = ["ldr R5"]

store :: Mem -> String
store (L x _) = "stl " ++ show x
store (H x _) = "sth " ++ show x
store (G x _) = "stl " ++ show x
store R5      = "str R5"

-- ldc 6
-- ldc 5
-- ldsa -1
-- sta 0
-- trap 0
-- Loads 6 and 5 on the stack. Gets the address of the 6.
-- and then sta 0 places the second argument (5) on the first arg (address of the 6)




-- ===== Local =====
-- Load Local. Pushes a value relative to the markpointer.
-- ldl :: Int -> String
-- ldl x = "ldl " ++ show x

-- stl :: Mem -> String
-- stl (L x _) = "stl " ++ show x
-- stl (H x _) = "stl " ++ show x

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

bsr :: String -> String 
bsr name = "bsr "++name

-- ===== Abitrary =====
-- Load Constant. Pushes the inline constant on the stack.
ldc :: Int -> String
ldc x = "ldc " ++ show x

lds :: Int -> String
lds x = "lds " ++ show x

-- Adjust Stack. Adjusts the stackpointer with fixed amount.
ajs :: Int -> String
ajs x = "ajs " ++ show x

-- ===== Heap =====
-- Load from Heap. Pushes a value pointed to by the value at the top of the stack. The pointer value is offset by a constant offset.
ldh :: Int -> String
ldh x = "ldl " ++ show x

-- Store into Heap. Pops 1 value from the stack and stores it into the heap. Pushes the heap address of that value on the stack.
sth :: Mem -> String 
sth (H x _) = "sth " ++ show x

-- ==================== Sorting ====================
sortSPL :: SPL -> ([Decl],[Decl])
sortSPL (SPL xs) = sortDecls (reverse xs)

sortDecls :: [Decl] -> ([Decl],[Decl])
sortDecls [] = ([],[])
sortDecls (VarMain x:xs) =  BI.first (VarMain x:) (sortDecls xs)
sortDecls (FuncMain (FunDecl (ID "main" l) args fType locals stmts):xs) = BI.second (\xs -> xs ++ [FuncMain (FunDecl (ID "main" l) args fType locals stmts)]) (sortDecls xs)
sortDecls (FuncMain x:xs) = BI.second (FuncMain x:) (sortDecls xs)

-- ==================== Main ====================

mainGenTest1 :: IO ()
mainGenTest1  = do
      file <- readFile  "../SPL_test_code/test1.spl"
      case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
            Right(_, _, spl) -> do
                let res = runGen (gen spl ["\n"] Map.empty)
                let (Right result,_) = res
                let output = intercalate "\n" (fst result)
                writeFile "../generated_ssm/gen.ssm" output
            Left x -> putStr $ "ERROR:\n" ++ show x ++ "\n" ++ showPlaceOfError file x


mainGen :: String -> IO ()
mainGen filename = do
      file <- readFile  ("../SPL_test_code/" ++ filename)
      case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
            Right(_, _, spl) -> do
                let res = runGen (gen spl ["\n"] Map.empty)
                let (Right result,_) = res
                let output = intercalate "\n" (fst result)
                writeFile "../generated_ssm/gen.ssm" output
            Left x -> putStr $ "ERROR:\n" ++ show x ++ "\n" ++ showPlaceOfError file x