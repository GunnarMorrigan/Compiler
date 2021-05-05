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
import Data.Set as Set
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
    G Int SPLType | -- Global
    L Int SPLType | -- Local
    H Int SPLType | -- Heap
    R5 -- Global Pointer
    deriving (Show, Eq)

data Scope = Global | Local
--               Ifs, Global, Overloaded function calls
type GenState = (Int, Int, (Map String FunCall, Map String Op2Typed))
type Gen a = ExceptT Error (State GenState) a
 
type GenEnv = Map IDLoc Mem

runGen :: Gen a -> (Either Error a, GenState)
runGen t = runState (runExceptT t) initState
  where initState = (0, 0, (Map.empty, Map.empty))

-- ===== State manipulation =====
resetIf :: Gen ()
resetIf = do
    (ifS,globalS, overloaded) <- get
    put (0,globalS, overloaded)

newIf :: String -> Gen (String, String, String)
newIf name = do  
    (ifS,globalS, overloaded) <- get
    put (ifS + 1,globalS, overloaded)
    return (name++"_ifTh"++show ifS, name++"_ifEl"++show ifS ,name++"_ifCon"++show ifS)

newGlobal :: SPLType -> Gen Mem
newGlobal typ = do
    (ifS,globalS, overloaded) <- get
    put (ifS,globalS + 1, overloaded)
    return $ G globalS typ

insertOp2 :: Op2Typed -> Gen ()
insertOp2 (Op2 op (Just (FunType t t'))) = do
    (ifS, globalS, (funcCalls, ops)) <- get
    put (ifS, globalS, (funcCalls, Map.insert (overloadedOpName op t) (Op2 op (Just (FunType t t'))) ops))

insertFunCall :: FunCall -> Gen ()
insertFunCall (FunCall (ID id loc) args (Just (FunType t t'))) = do
    (ifS, globalS, (funcCalls, ops)) <- get
    let f = Map.insert (overloadedTypeName id t) (FunCall (ID id loc) [] (Just $ FunType t t')) funcCalls
    put (ifS, globalS, (f, ops))

-- ===== Generation =====
genAssembly :: SPL -> Either Error [String]
genAssembly (SPL decls) = do
    let (rest, main) =  filterMain decls 
    case runGen (gen rest [] Map.empty) of
        (Left e, _) -> Left e
        (Right (ssmCodeWithoutMain, env), _) -> 
            case main of
                Nothing -> Left $ Error (-1) (-1) "No main without arguments detected"
                Just main' -> case runGen (gen main' [] env) of
                    (Left error, _) -> Left error 
                    (Right (ssmMain, _), (_, _, (overloadedFuns, overloadedOps))) -> 
                        Right $ ssmCodeWithoutMain ++ genOverloadedFuns overloadedFuns ++ ssmMain
    

filterMain :: [Decl] -> ([Decl], Maybe Decl)
filterMain [] = ([],Nothing)
filterMain (FuncMain (FunDecl (ID "main" loc) [] (Just fType) vDecls stmts):xs) = let(ys, main) = filterMain xs in (ys, Just (FuncMain(FunDecl (ID "main" loc) [] (Just fType) vDecls stmts)))
filterMain (x:xs) = let(ys, main) = filterMain xs in (x:ys, main)

class GenCode a where
    gen :: a -> [String] -> GenEnv -> Gen ([String], GenEnv)

instance GenCode a => GenCode [a] where
    gen [] c env = return (c, env)
    gen (x:xs) c env = do
        combineResult (gen x [] env) (gen xs c)

instance GenCode SPL where
    gen spl c env =
        let (globals, functions) = sortSPL spl in do
        combineResult (genGlobals globals [] env) (gen functions c)

instance GenCode Decl where
    gen (VarMain varDecl) c = genVarDecl varDecl c Global
    gen (FuncMain funDecl) c = gen funDecl c

genGlobals :: [Decl] -> [String] -> GenEnv -> Gen ([String], GenEnv)
genGlobals globals c env = do
    (res, env') <- gen globals ("bra main":c) env
    return ("ldsa 1":store R5:res, env')

genVarDecls :: [VarDecl] -> [String] -> Scope -> GenEnv -> Gen ([String], GenEnv)
genVarDecls [] c _ env = return (c,  env)
genVarDecls (x:xs) c s env = do
    combineResult (genVarDecl x [] s env) (genVarDecls xs c s)

genVarDecl :: VarDecl -> [String] -> Scope -> GenEnv -> Gen ([String], GenEnv)
genVarDecl (VarDeclType t id e) c Global env = {-- trace ("GLOBAL varDecl "++ show id ++ show env) $ --} do
    mem <- newGlobal t
    let env' = Map.insert id mem env
    let annotedC = ("annote SP 0 0 green \""++pp id ++ "\""):c
    insertComment (pp (VarDeclType t id e)) (gen e annotedC env')
genVarDecl (VarDeclType t i e) c Local env = case Map.lookup i env of
    Just memLoc -> gen e (store memLoc:c) env
    Nothing -> error ("Variable " ++ show i ++ " unkown in generator " ++ showLoc i)
genVarDecl (VarDeclVar _ _) c _ env = undefined

instance GenCode FunDecl where
    gen (FunDecl (ID "main" loc) [] (Just fType) vDecls stmts) c env = do
        resetIf
        let env' = constructEnv env fType [] vDecls
        
        (res,env'') <- combineResult (genVarDecls vDecls [] Local env') (genStmts stmts ("ldr RR":"trap 0":"halt":c) (ID "main" loc))

        return (insertLabel "main" (("link " ++ show (length vDecls)):res),env'')

    gen (FunDecl (ID name loc) args (Just fType) vDecls stmts) c env = do
        resetIf
        let env' = constructEnv env fType args vDecls
        
        (res, env'') <- combineResult
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
    (th, _, contin) <- newIf name

    (ifStmt, env') <- combineResult (gen e [brf contin] env) (genStmts stmts [] (ID name l))
    
    (rest, env'') <- genStmts xs c (ID name l) env'
    let rest' = insertLabel contin rest

    return $ if Prelude.null xs 
            then (ifStmt, env')
            else (ifStmt ++ rest, env'')
genStmts ((StmtIf e stmts (Just els) loc):xs) c (ID name l) env = do
    (th, _, contin) <- newIf name

    let elseBranchEnd = if Prelude.null xs then ["bra "++name++"End"] else [bra contin]

    (elseStmt, env') <- combineResult (gen e [brt th] env) (genStmts els elseBranchEnd (ID name l))

    (ifElseStmt, env'') <- genStmts stmts [] (ID name l) env'
    let ifElseStmt' = insertLabel th ifElseStmt

    (rest, env''') <- genStmts xs c (ID name l) env''
    let rest' = insertLabel contin rest

    return $ if Prelude.null xs 
                then (elseStmt++ifElseStmt++c, env'') 
                else (elseStmt++ifElseStmt++rest', env''') 
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
    Nothing -> return (retLink:c, env)
    Just e -> gen e ("ldr RR":retLink:c) env
genStmt stmt c _ env = throwError $ Error (-1) (-1) ("Failed to catch the following object:\n" ++ show stmt)

-- MAKE USE OF THE fType in funCall for overloading
genFuncCall :: FunCall -> [String] -> GenEnv -> Gen ([String], GenEnv)
genFuncCall (FunCall (ID "print" loc) args (Just (FunType (TypeBasic t loc') t'))) c env =
    case t of
        BasicInt  -> return ("trap 0":c, env)
        BasicChar -> return ("trap 1":c, env)
        BasicBool -> do
            let printName = overloadedTypeName "print" (TypeBasic t loc)
            insertFunCall (FunCall (ID "print" loc) args (Just (FunType (TypeBasic t loc) t')))
            return (bsr printName:c, env)
genFuncCall (FunCall (ID "print" loc) args (Just (FunType t t'))) c env = do
    let printName = overloadedTypeName "print" t
    insertFunCall (FunCall (ID "print" loc) args (Just (FunType t t')))
    return (bsr printName:c, env)
genFuncCall (FunCall (ID "isEmpty" _) args (Just fType)) c env = do
    gen args ("ldh 0":"ldc 0":"eq":c) env
genFuncCall (FunCall id args (Just fType)) c env = do
    let c' = (if Prelude.null args then c else ajs (negate $ length args):c)
    gen args (("bsr " ++ pp id):c') env

instance GenCode Exp where
    gen (ExpId id (Field [])) c env = case Map.lookup id env of
        Just mem -> return (load mem ++ c, env )
        Nothing -> error ("Variable " ++ show id ++ " unkown in generator " ++ showLoc id)
    gen (ExpId id (Field xs)) c env = case Map.lookup id env of
        Just mem -> return (load mem ++genStandardFunctions xs c, env)
        Nothing -> error ("Variable " ++ show id ++ " unkown in generator " ++ showLoc id)
    gen (ExpInt i _) c env = return (ldc i:c, env)
    gen (ExpBool b _) c env= return ( ldc (if b then -1 else 0  ):c, env)
    gen (ExpChar char _) c env = return (ldc (ord char):c, env)
    gen (ExpBracket e) c env = gen e c env
    
    gen (ExpEmptyList _) c env = 
            --  Value:Address
        return ("ldc 0":"ldc 0":"stmh 2":c, env)

    gen (ExpTuple (e1, e2) loc (Just (TupleType (t1,t2) _))) c env = do
        let storeTuple = "stmh 2":c
        combineResult (gen e2 [] env) (gen e1 storeTuple)
    
    gen (ExpFunCall funcall _) c env =
        genFuncCall funcall c env

    gen (ExpOp2 e1 op e2 loc) c env  = do
        let args = combineResult (gen e2 [] env) (gen e1 [])
        combineResult args (gen op c)
    gen (ExpOp1 op e loc) c env = case op of
        Neg -> gen e ("neg":c) env
        Not -> gen e ("not":c) env

genStandardFunctions :: [StandardFunction] -> [String] -> [String]
genStandardFunctions xs c = Prelude.foldr genStandardFunction c xs

genStandardFunction :: StandardFunction -> [String] -> [String]
genStandardFunction (Head _) c = "ldc 1":"sub":"ldh 0":c
genStandardFunction (Tail _) c = "ldh 0":c
genStandardFunction (First _) c = "ldh 0":c
genStandardFunction (Second _) c = "ldc 1":"sub":"ldh 0":c

instance GenCode Op2Typed where
    gen (Op2 Plus _) c env = return ("add":c, env)
    gen (Op2 Min _) c env = return ("sub":c, env)
    gen (Op2 Mult _) c env = return ("mul":c, env)
    gen (Op2 Div _) c env = return ("div":c, env)
    gen (Op2 Mod _) c env = return ("mod":c, env)

    gen (Op2 And _) c env = return ("and":c, env)
    gen (Op2 Or _) c env = return ("or":c, env)

    gen (Op2 Con (Just opType)) c env =
        return ("swp":"stmh 2":c,env)

    -- Should be extended for other types of comparison
    gen (Op2 op (Just (FunType (TypeBasic _ _) _))) c env = 
        return (op2Func op:c,env)
    gen (Op2 op (Just (FunType t t'))) c env = trace ("THIS IS the type:\n"++ show t) $ do
        let func = overloadedOpName op t
        return (bsr func:"ajs -2":"ldr RR":c, env)

-- ==================== Overloading functions ====================

overloadedTypeName :: String -> SPLType -> String
overloadedTypeName start t = start ++ typeToName t

overloadedOpName :: Op2 -> SPLType -> String
overloadedOpName op t = op2Func op ++ typeToName t

findOverloading :: [Decl] -> (Set FunCall,Set Exp)
findOverloading [] = (Set.empty, Set.empty)
findOverloading (x:xs) = findOverloading xs

genOverloadedFuns :: Map String FunCall -> [String]
genOverloadedFuns funs | Map.null funs  = []
genOverloadedFuns funs = do
    let (ssmCode, names) = genOverloadedFun (Map.elemAt 0 funs)
    let env = Map.filterWithKey (\ k _ -> k `elem` names) funs
    ssmCode ++ genOverloadedFuns env

genOverloadedFun :: (String, FunCall) -> ([String],[String])
genOverloadedFun (name, FunCall (ID "print" _) _ (Just (FunType t t'))) = 
    let (a,_,c) = genPrint t [] in (a,c)


-- genCompare :: Op2 -> SPLType -> [String] -> GenEnv -> Gen (String, [String], GenEnv)
-- genCompare op (TypeBasic _ _) c env = return (op2Func op,c,env)
-- genCompare op (TupleType (a,b) _) c env = do
--     let fName = op2Func op ++ "Tuple"
--     let check = brf (fName++"End")

--     let start = fName++":  link 0"

--     (bBSRfName, bC, env')  <- genCompare op b [] env
--     (aBSRfName, aC, env'') <- genCompare op a bC env'

--     let endBranch = [fName++"End:  unlink","    ret"]
--     let compareB = ["ldl -3","ldc 1","sub","ldh 0","ldl -2","ldc 1","sub","ldh 0",bBSRfName,"str RR"]
--     let compare = "ldl -3":"ldh 0":"ldl -2":"ldh 0":aBSRfName:"str RR":"ldr RR":check:compareB

--     return (fName, c ++ start:compare++endBranch++aC ,env'')

genPrint :: SPLType -> [String] -> ([String], String, [String])
genPrint (TypeBasic BasicInt _) c = (c,"trap 0" ,[])
genPrint (TypeBasic BasicChar _) c = (c,"trap 1", []) 
genPrint (TypeBasic BasicBool _) c = 
    ("printBool":c, bsr "printBool", ["printBool"])  
genPrint (TupleType (t1,t2) loc) c  = do
    let printName = "print" ++ typeToName (TupleType (t1,t2) loc)

    let (functionT1, printT1, printT1Names) = genPrint t1 c
    let (functions, printT2, printT2Names) = genPrint t2 functionT1

    let functionsC = (printName++":  link 0"): 
                        openBracket ("ldl -2":"ldh 0":printT1: 
                        comma ("ldl -2":"ldc 1":"sub":"ldh 0":printT2: 
                        closeBracket ("unlink":"ret":functions)))

    (functionsC, bsr printName, printName:(printT1Names++printT2Names)) 
genPrint (ArrayType a1 _) c  = undefined 

openBracket c  = "ldc 40":"trap 1":c
closeBracket c  = "ldc 41":"trap 1":c

openSqBracket c = "ldc 91":"trap 1":c
closeSqBracket c = "ldc 93":"trap 1":c

comma c = "ldc 44":"trap 1":c


typeToName :: SPLType -> String 
typeToName (TypeBasic x _) = pp x
typeToName (TupleType (t1,t2) _) = "Tuple" ++ typeToName t1 ++ typeToName t2
typeToName (ArrayType a1 _) = "Array"++ typeToName a1
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
    (resB, env') <- b env
    return (resA++resB, env')

-- combineEF :: Maybe [String] -> Maybe [String] -> Maybe [String]
-- combineEF Nothing x = x
-- combineEF x Nothing = x
-- combineEF (Just x) (Just y) = Just (x++y)

insertLabel :: String -> [String] -> [String]
insertLabel label (x:xs) = (label++":  "++x):xs

isVoidFun :: SPLType -> Bool
isVoidFun x = last (getArgsTypes x) `eqType` Void defaultLoc

insertComment :: String -> Gen ([String], GenEnv) -> Gen ([String], GenEnv)
insertComment comment c = BI.first f <$> c
    where f (x:xs) = (x++" //"++comment):xs

-- insertAnnote :: String Gen ([String], GenEnv) -> Gen ([String], GenEnv)

-- ==================== Environment ====================
constructEnv :: GenEnv -> SPLType -> [IDLoc] -> [VarDecl] -> GenEnv
constructEnv env fType xs ys = Map.fromList decls `Map.union` Map.fromList args `Map.union` env
    where
        args = zipWith3 (\ id loc typ -> (id, L loc typ)) xs [(negate (length xs)-1 )..] (init $ getArgsTypes fType)
        decls = zipWith (\(VarDeclType t id e) b -> (id, L b t) ) ys [1..]

-- ==================== Instructions ====================
load :: Mem -> [String] 
load (L x _) = ["ldl " ++ show x]
load (H x _) = undefined
load (G x t) = case x of
    0 -> load R5++["lda 0"]
    _ -> load R5++["ldc " ++ show x, "add", "lda 0"]
load R5      = ["ldr R5"]

store :: Mem -> String
store (L x _) = "stl " ++ show x
store (H x _) = "sth " ++ show x
store (G x _) = "stl " ++ show x
store R5      = "str R5"

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