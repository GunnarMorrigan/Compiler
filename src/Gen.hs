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
import Data.Bifunctor as BI
import Data.Set as Set
import Data.Map as Map
import Data.Either
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

newWhile :: String -> Gen String
newWhile name = do
    (ifS, globals, overloaded) <- get
    put (ifS + 1, globals, overloaded)
    return (name++"_while"++show ifS)

newGlobal :: SPLType -> Gen Mem
newGlobal typ = do
    (ifS,globalS, overloaded) <- get
    put (ifS,globalS + 1, overloaded)
    return $ G globalS typ

insertOp2 :: Op2Typed -> Gen ()
insertOp2 (Op2 op (Just t)) = do
    (ifS, globalS, (funcCalls, ops)) <- get
    put (ifS, globalS, (funcCalls, Map.insert (overloadedOpName op t) (Op2 op (Just t)) ops))

insertFunCall :: FunCall -> Gen ()
insertFunCall (FunCall (ID id loc) args (Just (FunType t t'))) = do
    (ifS, globalS, (funcCalls, ops)) <- get
    let f = Map.insert (overloadedTypeName id t) (FunCall (ID id loc) [] (Just $ FunType t t')) funcCalls
    put (ifS, globalS, (f, ops))

-- ===== Generation =====
genAssembly :: SPL -> Gen [String]
genAssembly (SPL decls) = do
    let (globals, functions, mainDecl) = sortDecls decls
    (assemblyGlobals, env) <- genGlobals globals [bsr "main"] Map.empty
    (assemblyFunctions, env') <- gen functions [] env
    case mainDecl of
        Nothing -> throwError $ Error defaultLoc "No main without arguments detected"
        Just main -> do
            (assemblyMain, _) <- gen main [] env'
            (_, _, (overloadedFuns, overloadedOps)) <- get 
            -- trace (show $ genOverloadedFun ( Map.elemAt 0 overloadedFuns) overloadedFuns) return $ assemblyBody ++ assemblyMain
            return $ 
                (assemblyGlobals ++ assemblyFunctions) ++ 
                    genOverloadedFuns overloadedFuns ++ 
                    genOverloadedOps overloadedOps ++
                assemblyMain

class GenCode a where
    gen :: a -> [String] -> GenEnv -> Gen ([String], GenEnv)

instance GenCode a => GenCode [a] where
    gen [] c env = return (c, env)
    gen (x:xs) c env = do
        combineResult (gen x [] env) (gen xs c)

instance GenCode SPL where
    gen (SPL spl) c env =
        gen spl c env

instance GenCode Decl where
    gen (VarMain varDecl) c = genVarDecl varDecl c Global
    gen (FuncMain funDecl) c = gen funDecl c

genGlobals :: [Decl] -> [String] -> GenEnv -> Gen ([String], GenEnv)
genGlobals [] c env = return (c,env)
genGlobals globals c env = do
    (res, env') <- gen globals c env
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
        
        (res,env'') <- combineResult (genVarDecls vDecls [] Local env') (genStmts stmts ("trap 0":"halt":c) (ID "main" loc))

        return (insertLabel "main" (("link " ++ show (length vDecls)):res),env'')
    gen (FunDecl (ID name loc) args (Just fType) vDecls stmts) c env = do
        resetIf
        let env' = constructEnv env fType args vDecls
        
        (res, env'') <- combineResult
                            (genVarDecls vDecls [] Local env')
                            (genStmts stmts (genReturn fType name c) (ID name loc))
        
        return (insertLabel name (("link " ++ show (length vDecls)):res),env'')
    gen (FunDecl (ID "main" loc) _ _ _ _) _ _ = 
        throwError $ Error loc "main function can't have arguments, return objects etc."

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
genStmts ((StmtWhile e stmts loc):xs) c (ID fname loc') env = do
    whileName <- newWhile fname
    let whileEnd = whileName++"End"
    let fEnd = fname++"End"
    (cond, envCond) <- gen e [] env
    (stmt, envStmt) <- genStmts stmts [] (ID fname loc') env
    (rst, envRst) <- genStmts xs c (ID fname loc') envStmt
    return $ if Prelude.null xs
        then (insertLabel whileName cond ++ [brf fEnd] ++ stmt ++ bra whileName:c, envStmt)
        else (insertLabel whileName cond ++ [brf whileEnd] ++ stmt ++ bra whileName :insertLabel whileEnd rst, envRst)
genStmts [StmtReturn exp loc] c id env =
    case exp of
        Nothing -> return (c, env)
        Just e -> gen e c env
genStmts (x:xs) c id env = do
    combineResult (genStmt x [] id env) (genStmts xs c id) 

genStmt :: Stmt -> [String] -> IDLoc -> GenEnv -> Gen ([String], GenEnv)
genStmt (StmtDeclareVar (ID name loc) (Field []) exp t) c _ env = 
    case Map.lookup (ID name loc) env of
        Nothing -> throwError $ Error loc ("Variable " ++ name ++ " unkown in generator " ++ showLoc loc) 
        Just mem -> do
            let storeVar = loadAddress mem ++ ["sta 0"]
            (assembly, env') <- gen exp storeVar env
            return (assembly++c, env') 
genStmt (StmtDeclareVar (ID name loc) (Field xs) exp (Just t)) c _ env = 
    case Map.lookup (ID name loc) env of
        Nothing -> throwError $ Error loc ("Variable " ++ name ++ " unkown in generator " ++ showLoc loc) 
        Just mem -> do
            let storeVar = load mem ++ genSFuncsAddress xs ["sta 0"]
            (assembly, env') <- gen exp storeVar env
            return (assembly++c, env') 
genStmt (StmtFuncCall funcall _) c _ env = 
    genFuncCall funcall c env
genStmt (StmtReturn exp loc) c (ID id _) env =
    let retLink = "bra " ++ id ++ "End"
    in case exp of
        Nothing -> return (retLink:c, env)
        Just e -> gen e ("str RR":retLink:c) env
genStmt stmt c _ env = throwError $ Error defaultLoc ("Failed to catch the following object:\n" ++ show stmt)

genFuncCall :: FunCall -> [String] -> GenEnv -> Gen ([String], GenEnv)
genFuncCall (FunCall (ID "print" loc) args (Just (FunType (TypeBasic t loc') t'))) c env =
    case t of
        BasicInt  -> gen args ("trap 0":c) env
        BasicChar -> gen args ("trap 1":c) env
        BasicBool -> do
            let printName = overloadedTypeName "print" (TypeBasic t loc)
            insertFunCall (FunCall (ID "print" loc) args (Just (FunType (TypeBasic t loc) t')))
            gen args (bsr printName:ajs (-1):c) env
genFuncCall (FunCall (ID "print" loc) args (Just (FunType t t'))) c env = do
    let printName = overloadedTypeName "print" t
    insertFunCall (FunCall (ID "print" loc) args (Just (FunType t t')))
    gen args (bsr printName:ajs (-1):c) env
genFuncCall (FunCall (ID "isEmpty" _) args (Just fType)) c env = do
    gen args ("ldh 0":"ldc 0":"eq":c) env
genFuncCall (FunCall id args (Just fType)) c env = do
    let c' = (if isVoidFun fType then c else "ldr RR":c)
    let c'' = (if Prelude.null args then c' else ajs (negate $ length args):c')
    gen args (bsr (pp id):c'') env

instance GenCode Exp where
    gen (ExpId id (Field [])) c env = case Map.lookup id env of
        Just mem -> return (load mem ++ c, env )
        Nothing -> error ("Variable " ++ show id ++ " unkown in generator " ++ showLoc id)
    gen (ExpId id (Field xs)) c env = case Map.lookup id env of
        Just mem -> return (load mem ++ genStandardFunctions xs c, env)
        Nothing -> error ("Variable " ++ show id ++ " unkown in generator " ++ showLoc id)
    gen (ExpInt i _) c env = return (ldc i:c, env)
    gen (ExpBool b _) c env= return ( ldc (if b then -1 else 0  ):c, env)
    gen (ExpChar char _) c env = return (ldc (ord char):c, env)
    gen (ExpBracket e) c env = gen e c env 
    gen (ExpEmptyList _) c env = 
        return ("ldc 0":"ldc 0":"stmh 2":c, env)
    gen (ExpTuple (e1, e2) loc (Just (TupleType (t1,t2) _))) c env = do
        let storeTuple = "stmh 2":c
        combineResult (gen e2 [] env) (gen e1 storeTuple)   
    gen (ExpFunCall funcall _) c env =
        genFuncCall funcall c env

    gen (ExpOp2 e1 op e2 loc) c env  = do
        (operator, env') <- gen op c env
        (secondArg, env'') <- gen e2 operator env'
        gen e1 secondArg env''
    gen (ExpOp1 op e loc) c env = case op of
        Neg -> gen e ("neg":c) env
        Not -> gen e ("not":c) env

genSFuncsAddress :: [StandardFunction] -> [String] -> [String]
genSFuncsAddress [] c = c
genSFuncsAddress xs c = 
    let offset = genSFuncsOffSet xs 
    in case offset of
        0 ->c
        _ -> ("ldc "++ show (genSFuncsOffSet xs)):"add":c

genSFuncsOffSet :: [StandardFunction] -> Int
genSFuncsOffSet [] = 0
genSFuncsOffSet ((Head _):xs) = genSFuncsOffSet xs - 1
genSFuncsOffSet ((Second _):xs) = genSFuncsOffSet xs - 1
genSFuncsOffSet ((Tail _):xs) = genSFuncsOffSet xs
genSFuncsOffSet ((First _):xs) = genSFuncsOffSet xs

genStandardFunctions :: [StandardFunction] -> [String] -> [String]
genStandardFunctions xs c = Prelude.foldr genStandardFunction c xs

genStandardFunction :: StandardFunction -> [String] -> [String]
genStandardFunction (Head _) c = "ldh -1":c
genStandardFunction (Tail _) c = "ldh 0":c
genStandardFunction (First _) c = "ldh 0":c
genStandardFunction (Second _) c = "ldh -1":c

instance GenCode Op2Typed where
    gen (Op2 Plus _) c env = return ("add":c, env)
    gen (Op2 Min _) c env = return ("sub":c, env)
    gen (Op2 Mult _) c env = return ("mul":c, env)
    gen (Op2 Div _) c env = return ("div":c, env)
    gen (Op2 Mod _) c env = return ("mod":c, env)

    gen (Op2 And _) c env = return ("and":c, env)
    gen (Op2 Or _) c env = return ("or":c, env)

    gen (Op2 Con (Just opType)) c env =
        return ("stmh 2":c,env)

    gen (Op2 op (Just (FunType (TypeBasic BasicBool _) _))) c env = 
        case op of
            Le  -> return ("gt":c,env)
            Ge  -> return ("lt":c,env)
            Leq -> return ("ge":c,env)
            Geq -> return ("ne":c,env)
            _   -> return (op2Func op:c,env)
    gen (Op2 op (Just (FunType (TypeBasic _ _) _))) c env = 
        return (op2Func op:c,env)
    gen (Op2 op (Just (FunType t t'))) c env = trace ("THIS IS the type:\n"++ pp t) $ do
        let func = overloadedOpName op t
        insertOp2 (Op2 op (Just t))
        return (bsr func:"ajs -2":"ldr RR":c, env)

-- ==================== Overloading functions ====================

overloadedTypeName :: String -> SPLType -> String
overloadedTypeName start t = start ++ typeToName t

overloadedOpName :: Op2 -> SPLType -> String
overloadedOpName op t = op2Func op ++ typeToName t

genOverloadedOps :: Map String Op2Typed -> [String]
genOverloadedOps ops | Map.null ops  = []
genOverloadedOps ops = do
    let (ssmCode, ops') = genOverloadedOp (Map.elemAt 0 ops) ops
    ssmCode ++ genOverloadedOps ops'

genOverloadedOp :: (String, Op2Typed) -> Map String Op2Typed -> ([String], Map String Op2Typed)
genOverloadedOp (_,Op2 op (Just t)) env = (\(a,b,c) -> (b,c)) $ genCompare op t [] env

genOverloadedFuns :: Map String FunCall -> [String]
genOverloadedFuns funcs | Map.null funcs  = []
genOverloadedFuns funcs = do
    let (ssmCode, funcs') = genOverloadedFun (Map.elemAt 0 funcs) funcs
    ssmCode ++ genOverloadedFuns funcs'

genOverloadedFun :: (String, FunCall) ->  Map String FunCall -> ([String], Map String FunCall)
genOverloadedFun (name, FunCall (ID "print" _) _ (Just (FunType t t'))) funcs = 
   (\(a,b,c) -> (b,c)) $ genPrint t [] funcs

genPrint :: SPLType -> [String] -> Map String FunCall -> (String, [String], Map String FunCall)
genPrint (TypeBasic BasicInt _) c funcs = ("trap 0", c ,funcs)
genPrint (TypeBasic BasicChar _) c funcs = ("trap 1", c, funcs) 
genPrint (TypeBasic BasicBool _) c funcs = do
    let functionsC = "printBool:  link 0":"ldl -2":"brf printFalse":
                        "ldc 101":"ldc 117":"ldc 114":"ldc 84":
                            "trap 1":"trap 1":"trap 1":"trap 1":"unlink":"ret":
                        "printFalse:  ldc 101":"ldc 115":"ldc 108":"ldc 97":"ldc 70":
                            "trap 1":"trap 1":"trap 1":"trap 1":"trap 1":"unlink":"ret":c
    (bsr "printBool", functionsC, Map.delete "printBool" funcs)
genPrint (TupleType (t1,t2) loc) c funcs = do
    let printName = "print" ++ typeToName (TupleType (t1,t2) loc)

    let (printT1, functionT1, funcs') = genPrint t1 c funcs
    let (printT2, functions, funcs'') = genPrint t2 functionT1 funcs'

    let functionsC = (printName++":  link 0"): 
                        openBracket ("ldl -2":"ldh 0":printT1: 
                        comma ("ldl -2":"ldh -1":printT2: 
                        closeBracket ("unlink":"ret":functions)))
    (bsr printName, functionsC, Map.delete printName funcs'') 
genPrint (ArrayType a loc) c funcs = do
    let printName  = "print" ++ typeToName (ArrayType a loc)
    let (printA, functionT1, funcs') = genPrint a c funcs

    -- let endList = insertLabel "EmptyList" (closeSqBracket ["unlink","ret"])
    -- let functionsC = (printName++": link 0") : openSqBracket ("ldl -2":"ldc 0":"eq":"brt EmptyList":"ldl -2":"ldh -1":printA:"ldl -2":"ldh 0":bsr printName:endList)

    let functionsC = printArray printA printName

    (bsr printName, functionsC ++ functionT1 ++ c, Map.delete printName funcs)

printArray :: String -> String -> [String]
printArray printA printName = [printName ++": link 1",
    "ldl -2",
    "stl 1",
    "ldc 91",
    "trap 1",
    "ldl 1",
    "ldh 0",
    "ldc 0",
    "eq",
    brt printName++"End",
    "ldl 1",
    "ldh -1",
    printA,
    "ldl 1",
    "ldh 0",
    "str R7",
    "ldr R7",
    "ldh 0",
    "ldc 0",
    "eq",
    brt printName++"End",
    "ldc 44",
    "trap 1",
    "ldr R7",
    "stl 1",
    "ldr PC",
    "ldc 0x28",
    "sub",
    "str PC",
    printName++"End:  ldc 93",
    "trap 1",
    "unlink",
    "ret"]


genCompare :: Op2 -> SPLType -> [String] -> Map String Op2Typed -> (String, [String], Map String Op2Typed)
genCompare op (TypeBasic BasicBool _) c env = case op of
            Le  -> ("gt",c,env)
            Ge  -> ("lt",c,env)
            Leq -> ("ge",c,env)
            Geq -> ("ne",c,env)
            _   -> (op2Func op,c,env)
genCompare op (TypeBasic _ _) c env = (op2Func op, c, env)
genCompare op (TupleType (t1,t2) loc) c env = do
    let opName = op2Func op ++ typeToName (TupleType (t1,t2) loc)
    let (t1Name, functionT1, env') = genCompare op t1 c env
    let (t2Name, functionT2, env'') = genCompare op t2 functionT1 env'
    let check = brf (opName++"End")
    let endBranch = (opName++"End:  unlink"):"    ret":functionT2
    let compare2 = "ldl -3":"ldh -1":"ldl -2":"ldh -1":t2Name:"str RR":endBranch
    let compare1 = (opName++":  link 0"):"ldl -3":"ldh 0":"ldl -2":"ldh 0":t1Name:"str RR":"ldr RR":check:compare2
    (bsr opName, compare1 , Map.delete opName env'') 
genCompare op (ArrayType a loc) c env = do
    let opName = op2Func op ++ typeToName (ArrayType a loc)
    let (opExecA, function, env') = genCompare op a c env
    let functionsC = compArray opExecA opName
    (bsr opName, functionsC ++ function ++ c, Map.delete opName env)

compArray :: String -> String -> [String]
compArray compareA compName = 
    [compName ++": link 2",
    "ldl -3",
    "stl 1",
    "ldl -2",
    "stl 2",
    "ldl 1 //End of first list?", 
    "ldh 0",
    "ldc 0",
    "eq",
    "ldl 2 //End of sec list?",
    "ldh 0",
    "ldc 0",
    "eq",
    "add",
    "ldc 0",
    "lt //Any list (or both) Empty?",
    "str RR",
    "ldr RR",
    brt compName++"End",
    "ldl 1",
    "ldh -1",
    "ldl 2",
    "ldh -1",
    compareA,
    "str RR",
    "ldr RR",
    brf compName++"End",
    "ldl 1",
    "ldh 0",
    "stl 1",
    "ldl 2",
    "ldh 0",
    "stl 2",
    "ldr R7",
    "ldr PC",
    "ldc 0x37",
    "sub",
    "str PC",
    compName++"End:  unlink",
    "ret"]

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
typeToName x = trace ("Error we did not catch type"++ pp x) undefined 

op2Func :: Op2 -> String
op2Func Le  = "lt"
op2Func Ge  = "gt"
op2Func Leq = "le"
op2Func Geq = "ge"
op2Func Eq  = "eq"
op2Func Neq = "ne"

-- ==================== Sorting ====================
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

-- ==================== Helper functions ====================
combineResult :: Gen ([String], GenEnv) -> (GenEnv -> Gen ([String], GenEnv)) -> Gen ([String], GenEnv)
combineResult a b = do
    (resA, env) <- a
    (resB, env') <- b env
    return (resA++resB, env')

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
loadAddress :: Mem -> [String] 
loadAddress (L x _) = ["ldla " ++ show x]
loadAddress (H x _) = undefined
loadAddress (G x t) = case x of
    0 -> load R5
    _ -> load R5++["ldc " ++ show x, "add"]
loadAddress R5      = ["ldr R5"]

load :: Mem -> [String] 
load (L x _) = ["ldl " ++ show x]
load (H x _) = undefined
load (G x t) = load R5++["lda "++show x]
load R5      = ["ldr R5"]

store :: Mem -> String
store (L x _) = "stl " ++ show x
store (H x _) = undefined
store (G x _) = "stl " ++ show x
store R5      = "str R5"

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
            Right(_, _, spl) ->
                case runGen $ genAssembly spl of
                    (Right result,_) -> do
                                let output = intercalate "\n" result
                                writeFile "../generated_ssm/gen.ssm" output
                    (Left x,_) -> putStr $ "ERROR:\n" ++ show x ++ "\n" ++ showPlaceOfError file x
            Left x -> putStr $ "ERROR:\n" ++ show x ++ "\n" ++ showPlaceOfError file x