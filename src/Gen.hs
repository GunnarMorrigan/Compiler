{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Gen where

import AST
import Error
import Parser
import MutRec
import TI
import Ssm

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
import Prelude hiding ()

-- ===== Types ====
data Mem =
    G Int SPLType | -- Global
    L Int SPLType | -- Local
    R Register              -- Global Pointer
    deriving (Show, Eq)

--               Ifs, Global, Overloaded functions, overloaded Op2s
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
    return ('_':name++"_ifTh"++show ifS, name++"_ifEl"++show ifS ,name++"_ifCon"++show ifS)

newWhile :: String -> Gen String
newWhile name = do
    (ifS, globals, overloaded) <- get
    put (ifS + 1, globals, overloaded)
    return ('_':name++"_while"++show ifS)

newGlobal :: SPLType -> Gen Mem
newGlobal typ = do
    (ifS,globalS, overloaded) <- get
    put (ifS,globalS + 1, overloaded)
    return $ G globalS typ

insertOp2 :: Op2Typed -> Gen ()
insertOp2 (Op2 op (Just t) loc) = do
    (ifS, globalS, (funcCalls, ops)) <- get
    put (ifS, globalS, (funcCalls, Map.insert (overloadedOpName op t) (Op2 op (Just t) loc) ops))

insertFunCall :: FunCall -> Gen ()
insertFunCall (FunCall (ID locA id locB) args (Just (FunType t t'))) = do
    (ifS, globalS, (funcCalls, ops)) <- get
    let f = Map.insert (overloadedTypeName id t) (FunCall (ID locA id locB)[] (Just $ FunType t t')) funcCalls
    put (ifS, globalS, (f, ops))

-- ===== Generation =====
genSPL :: SPL -> Gen SSM
genSPL spl = do
    let (globals, functions, mainDecl) = sortSPL spl
    (assemblyGlobals, env) <- trace "1" $ genGlobals globals Map.empty
    (assemblyFunctions, env') <- trace "2" $ genFunDecls functions env
    case mainDecl of
        Nothing -> throwError $ Error defaultLoc "No main without arguments detected"
        Just main -> do
            (assemblyMain, _) <- trace "3" $ genFunDecl main env'
            (_, _, (overloadedFuns, overloadedOps)) <- get 
            return $ 
                SSM assemblyGlobals $
                    assemblyFunctions ++
                    genOverloadedFuns overloadedFuns ++ 
                    genOverloadedOps overloadedOps ++
                    [assemblyMain]

genGlobals :: [VarDecl] -> GenEnv -> Gen ([SsmGlobal], GenEnv)
genGlobals [] env = return ([],env)
genGlobals (g:gs) env = do
    (g', env') <- genVarDecl g [] GlobalScope env
    (res, env'') <- genGlobals gs env'
    return (Ssm.Global g':res, env'')

genVarDecls :: [VarDecl] -> [Instruct] -> Scope -> GenEnv -> Gen ([Instruct], GenEnv)
genVarDecls [] c _ env = return (c,  env)
genVarDecls (x:xs) c s env = do
    combineResult (genVarDecl x [] s env) (genVarDecls xs c s)

genVarDecl :: VarDecl -> [Instruct] -> Scope -> GenEnv -> Gen ([Instruct], GenEnv)
genVarDecl (VarDeclType t id e) c GlobalScope env = do
    mem <- newGlobal t
    let env' = Map.insert id mem env
    -- let annotedC = ("annote SP 0 0 green \""++pp id ++ "\""):c
    insertComment (pp (VarDeclType t id e)) (genExp e c env')
genVarDecl (VarDeclType t i e) c LocalScope env = case Map.lookup i env of
    Just memLoc -> genExp e (store memLoc:c) env
    Nothing -> error ("Variable " ++ show i ++ " unkown in generator " ++ showLoc i)
genVarDecl (VarDeclVar _ _) c _ env = undefined

genFunDecls :: [FunDecl] -> GenEnv -> Gen ([SsmFunction], GenEnv)
genFunDecls [] env = return ([],env)
genFunDecls (f:fs) env = do
    (f', env') <- genFunDecl f env
    (res, env') <- genFunDecls fs env
    return (f':res, env')

genFunDecl :: FunDecl -> GenEnv -> Gen (SsmFunction, GenEnv)
genFunDecl (FunDecl (ID locA "main" locB) [] (Just fType) vDecls stmts) env = do
    resetIf
    let env' = constructEnv env fType [] vDecls
    
    (res,env'') <- combineResult (genVarDecls vDecls [] LocalScope env') (genStmts stmts [HALT] (ID locA "main" locB))

    return (Function "main" (LABEL "main" (LINK (length vDecls)):res), env'')
genFunDecl (FunDecl (ID locA name locB) args (Just fType) vDecls stmts) env = do
    resetIf
    let env' = constructEnv env fType args vDecls
    
    (res, env'') <- combineResult
                        (genVarDecls vDecls [] LocalScope env')
                        (genStmts stmts (genReturn fType name []) (ID locA name locB))
    
    return (Function name (LABEL name (LINK (length vDecls)):res), env'')
genFunDecl (FunDecl (ID locA "main" locB) _ _ _ _) _ = 
    throwError $ ErrorD (DLoc locA locB) "main function can't have arguments, return objects etc."

genReturn :: SPLType -> String -> [Instruct] -> [Instruct]
genReturn fType fName c | isVoidFun fType = LABEL (fName++"End") UNLINK:RET:c
genReturn fType fName c = LABEL (fName++"End") (STR RR):UNLINK:RET:c

genStmts :: [Stmt] -> [Instruct] -> IDLoc -> GenEnv -> Gen ([Instruct], GenEnv)
genStmts [] c id env = return (c, env)
-- The following two are here and not in genStmt because here we know if we need a continuation for something after the if stmt.
genStmts ((StmtIf e stmts Nothing loc):xs) c id env = do
    let (ID _ fname _) = id
    (th, _, contin) <- newIf fname

    (ifStmt, env') <- combineResult (genExp e [BRF contin] env) (genStmts stmts [] id)
    
    (rest, env'') <- genStmts xs c id env'
    let rest' = insertLabel contin rest

    return $ if Prelude.null xs 
            then (ifStmt, env')
            else (ifStmt ++ rest, env'')
genStmts ((StmtIf e stmts (Just els) loc):xs) c id env = do
    let (ID _ fname _) = id
    (th, _, contin) <- newIf fname

    let elseBranchEnd = if Prelude.null xs then [BRA (fname++"End")] else [BRA contin]

    (elseStmt, env') <- combineResult (genExp e [BRT th] env) (genStmts els elseBranchEnd id)

    (ifElseStmt, env'') <- genStmts stmts [] id env'
    let ifElseStmt' = insertLabel th ifElseStmt

    (rest, env''') <- genStmts xs c id env''
    let rest' = insertLabel contin rest

    return $ if Prelude.null xs 
                then (elseStmt++ifElseStmt++c, env'') 
                else (elseStmt++ifElseStmt++rest', env''')
genStmts ((StmtWhile e stmts loc):xs) c id env = do
    let (ID _ fname _) = id
    whileName <- newWhile fname
    let whileEnd = whileName++"End"
    let fEnd = fname++"End"
    (cond, envCond) <- genExp e [] env
    (stmt, envStmt) <- genStmts stmts [] id env
    (rst, envRst) <- genStmts xs c id envStmt
    return $ if Prelude.null xs
        then (insertLabel whileName cond ++ [BRF fEnd] ++ stmt ++ BRA whileName:c, envStmt)
        else (insertLabel whileName cond ++ [BRF whileEnd] ++ stmt ++ BRA whileName :insertLabel whileEnd rst, envRst)
genStmts [StmtReturn exp loc] c id env =
    case exp of
        Nothing -> return (c, env)
        Just e -> genExp e c env
genStmts (x:xs) c id env = do
    combineResult (genStmt x [] id env) (genStmts xs c id) 

genStmt :: Stmt -> [Instruct] -> IDLoc -> GenEnv -> Gen ([Instruct], GenEnv)
genStmt (StmtAssignVar (ID locA name locB) (Field []) exp t) c _ env = 
    case Map.lookup (ID locA name locB) env of
        Nothing -> throwError $ ErrorD (DLoc locA locB) ("Variable " ++ name ++ " unkown in generator " ++ showLoc locA) 
        Just mem -> do
            let storeVar = loadAddress mem ++ [STA 0]
            (assembly, env') <- genExp exp storeVar env
            return (assembly++c, env') 
genStmt (StmtAssignVar (ID locA name locB) (Field xs) exp (Just t)) c _ env = 
    case Map.lookup (ID locA name locB) env of
        Nothing -> throwError $ ErrorD (DLoc locA locB) ("Variable " ++ name ++ " unkown in generator " ++ showLoc locA) 
        Just mem -> do
            let storeVar = load mem ++ genSFuncsAddress xs [STA 0]
            (assembly, env') <- genExp exp storeVar env
            return (assembly++c, env') 
genStmt (StmtFuncCall funcall _) c _ env = 
    genFuncCall funcall c env
genStmt (StmtReturn exp loc) c (ID locA name locB) env =
    let retLink = BRA (name ++ "End")
    in case exp of
        Nothing -> return (retLink:c, env)
        Just e -> genExp e (STR RR:retLink:c) env
genStmt stmt c (ID locA name locB) env = throwError $ Error defaultLoc ("Failed to catch an statement in function " ++ name ++" object:\n" ++ show stmt)

genFuncCall :: FunCall -> [Instruct] -> GenEnv -> Gen ([Instruct], GenEnv)
genFuncCall (FunCall (ID locA "print" locB) args (Just (FunType (TypeBasic locA' t locB') t'))) c env =
    case t of
        BasicInt  -> genExps args (TRAP 0:c) env
        BasicChar -> genExps args (TRAP 1:c) env
        BasicBool -> do
            let printName = overloadedTypeName "print" (TypeBasic locA' t locB')
            insertFunCall (FunCall (ID locA "print" locB) args (Just (FunType (TypeBasic locA'  t locB') t')))
            genExps args (BSR printName:AJS (-1):c) env
-- genFuncCall (FunCall (ID locA "print" locB) args (Just (FunType (ArrayType locA' (IdType id) locB') t'))) c env = do
--     let printName = "_printPolyEmptyList"
--     genExps args (COMMENT (LDC 91) "_printPolyEmptyList":TRAP 1:LDC 93:TRAP 1:c) env
genFuncCall (FunCall (ID locA "print" locB) args (Just (FunType t t'))) c env = do
    let printName = overloadedTypeName "print" t
    insertFunCall (FunCall (ID locA "print" locB) args (Just (FunType t t')))
    genExps args (BSR printName:AJS (-1):c) env
genFuncCall (FunCall (ID _ "isEmpty" _) args (Just fType)) c env = do
    genExps args (LDC 0:Ssm.EQ:c) env
genFuncCall (FunCall id args (Just fType)) c env = do
    let c' = (if isVoidFun fType then c else LDR RR:c)
    let c'' = (if Prelude.null args then c' else AJS (negate $ length args):c')
    genExps args (BSR (pp id):c'') env

genExps :: [Exp] -> [Instruct] -> GenEnv -> Gen ([Instruct], GenEnv)
genExps [] c env = return (c,env)
genExps (x:xs) c env = do
    (ass, env') <- genExp x [] env
    (res, env'') <- genExps xs c env'
    return (ass++res, env'')

genExp :: Exp -> [Instruct] -> GenEnv -> Gen ([Instruct], GenEnv)
genExp (ExpId id (Field [])) c env = case Map.lookup id env of
    Just mem -> return (load mem ++ c, env )
    Nothing -> error ("Variable " ++ show id ++ " unkown in generator " ++ showLoc id)
genExp (ExpId id (Field xs)) c env = case Map.lookup id env of
    Just mem -> return (load mem ++ genStandardFunctions xs c, env)
    Nothing -> error ("Variable " ++ show id ++ " unkown in generator " ++ showLoc id)
genExp (ExpInt _ i _) c env = return (LDC i:c, env)
genExp (ExpBool _ b _) c env= return ( LDC (if b then -1 else 0  ):c, env)
genExp (ExpChar _ char _) c env = return (LDC (ord char):c, env)
genExp (ExpBracket e) c env = genExp e c env 
genExp (ExpEmptyList _ _) c env = 
    return (LDC 0:c, env)
genExp (ExpTuple _ (e1, e2) _ (Just (TupleType _ (t1,t2) _))) c env = do
    let storeTuple = STMH 2:c
    combineResult (genExp e2 [] env) (genExp e1 storeTuple)   
genExp (ExpFunCall _ funcall _) c env =
    genFuncCall funcall c env
genExp (ExpOp2 _ e1 op e2 _) c env  = do
    (operator, env') <- genOp2Typed op c env
    (secondArg, env'') <- genExp e2 operator env'
    genExp e1 secondArg env''
genExp (ExpOp1 _ op e _) c env = case op of
    Neg -> genExp e (NEG:c) env
    Not -> genExp e (NOT:c) env

genSFuncsAddress :: [StandardFunction] -> [Instruct] -> [Instruct]
genSFuncsAddress [] c = c
genSFuncsAddress xs c = 
    let offset = genSFuncsOffSet xs 
    in case offset of
        0 ->c
        _ -> LDC (genSFuncsOffSet xs):ADD:c

genSFuncsOffSet :: [StandardFunction] -> Int
genSFuncsOffSet [] = 0
genSFuncsOffSet ((Head _ _):xs) = genSFuncsOffSet xs - 1
genSFuncsOffSet ((Snd _ _):xs) = genSFuncsOffSet xs - 1
genSFuncsOffSet ((Tail _ __):xs) = genSFuncsOffSet xs
genSFuncsOffSet ((Fst _ _):xs) = genSFuncsOffSet xs

genStandardFunctions :: [StandardFunction] -> [Instruct] -> [Instruct]
genStandardFunctions xs c = Prelude.foldr genStandardFunction c xs

genStandardFunction :: StandardFunction -> [Instruct] -> [Instruct]
genStandardFunction (Head _ _) c = LDH (-1):c
genStandardFunction (Tail _ _) c = LDH 0:c
genStandardFunction (Fst _ _) c = LDH 0:c
genStandardFunction (Snd _ _) c = LDH (-1):c

genOp2Typed :: Op2Typed -> [Instruct] -> b -> Gen ([Instruct], b)
genOp2Typed (Op2 Plus _ _) c env = return (ADD:c, env)
genOp2Typed (Op2 Min _ _) c env = return (SUB:c, env)
genOp2Typed (Op2 Mult _ _) c env = return (MUL:c, env)
genOp2Typed (Op2 Div _ _) c env = return (DIV:c, env)
genOp2Typed (Op2 Mod _ _) c env = return (MOD:c, env)

genOp2Typed (Op2 And _ _) c env = return (AND:c, env)
genOp2Typed (Op2 Or _ _) c env = return (OR:c, env)

genOp2Typed (Op2 Con _ _) c env =
    return (STMH 2:c,env)

genOp2Typed (Op2 op (Just (FunType (TypeBasic _ BasicBool _) _))_) c env = 
    case op of
        Le  -> return (Ssm.GT:c,env)
        Ge  -> return (Ssm.LT:c,env)
        Leq -> return (Ssm.GE:c,env)
        Geq -> return (Ssm.NE:c,env)
        _   -> return (op2Func op:c,env)
genOp2Typed (Op2 op (Just (FunType (ArrayType _ (IdType _) _) _))_) c env =
    return (op2Func op:c,env)
genOp2Typed (Op2 op (Just (FunType TypeBasic{} _))_) c env = 
    return (op2Func op:c,env)
genOp2Typed (Op2 op (Just (FunType t t')) loc) c env = trace ("THIS IS the type:\n"++ pp t) $ do
    let func = overloadedOpName op t
    insertOp2 (Op2 op (Just t) loc)
    return (BSR func:AJS (-2):LDR RR:c, env)

-- ==================== Overloading functions ====================
overloadedTypeName :: String -> SPLType -> String
overloadedTypeName start t = '_':start ++ typeToName t

overloadedOpName :: Op2 -> SPLType -> String
overloadedOpName op t = '_':op2String op ++ typeToName t

genOverloadedFuns :: Map String FunCall -> [SsmFunction]
genOverloadedFuns funcs = concatMap (snd . genPrint) $ Map.elems (getOverloadedFuns (Map.toList funcs))

getOverloadedFuns :: [(String, FunCall)] -> Map String SPLType
getOverloadedFuns [] = Map.empty
getOverloadedFuns ((name, FunCall (ID _ "print" _) _ (Just (FunType t t'))):xs) = 
    getOverloadedFun "print" t `Map.union` getOverloadedFuns xs

getOverloadedFun :: String -> SPLType -> Map String SPLType
getOverloadedFun funcName (TypeBasic _ BasicInt _) = Map.empty 
getOverloadedFun funcName (TypeBasic _ BasicChar _) = Map.empty 
getOverloadedFun funcName (TypeBasic locA BasicBool locB) = 
    let name = overloadedTypeName funcName (TypeBasic locA BasicBool locB)
    in Map.singleton name (TypeBasic locA BasicBool locB)
getOverloadedFun funcName (TupleType locA (t1,t2) locB) = 
    let name = overloadedTypeName funcName (TupleType locA (t1,t2) locB) 
    in Map.singleton name (TupleType locA (t1,t2) locB) `Map.union` getOverloadedFun funcName t1 `Map.union` getOverloadedFun funcName t2
getOverloadedFun funcName (ArrayType locA a locB) =
    let name = overloadedTypeName funcName (ArrayType locA a locB)
    in Map.singleton name (ArrayType locA a locB) `Map.union` getOverloadedFun funcName a
getOverloadedFun funcName t = trace ("Unexpected input in getOverloadedFun: "++funcName ++ " with type: " ++ pp t) undefined  

genPrint :: SPLType -> (Instruct, [SsmFunction])
genPrint (TypeBasic _ BasicInt _) = (TRAP 0, [])
genPrint (TypeBasic _ BasicChar _) = (TRAP 1, []) 
genPrint (TypeBasic _ BasicBool _) = do
    let function = [LABEL "_printBool"  (LINK 0),LDL (-2),BRF "_printFalse",
                        LDC 101,LDC 117,LDC 114,LDC 84,
                            TRAP 1,TRAP 1,TRAP 1,TRAP 1,UNLINK,RET,
                        LABEL "_printFalse" (LDC 101),LDC 115,LDC 108,LDC 97,LDC 70,
                            TRAP 1,TRAP 1,TRAP 1,TRAP 1,TRAP 1,UNLINK,RET]
    (BSR "_printBool", [Function "_printBool" function])
genPrint (TupleType locA (t1,t2) locB)  = do
    let printName = overloadedTypeName "print" (TupleType locA (t1,t2) locB)

    let (printT1, functionT1) = genPrint t1 
    let (printT2, functionT1T2) = genPrint t2 

    let function = LABEL printName (LINK 0): 
                        openBracket (LDL (-2):LDH 0:printT1: 
                        comma (LDL (-2):LDH (-1):printT2: 
                        closeBracket [UNLINK,RET]))

    (BSR printName, [Function printName function]) 
genPrint (ArrayType _ (IdType _) loc) = do
    let printName  = "_printPolyEmptyList"

    let functions = printArray NOP printName
    (BSR printName, [Function printName functions]) 
genPrint (ArrayType locA a locB) = do
    let printName  = overloadedTypeName "print" (ArrayType locA a locB)
    let (printA, functionT1) = genPrint a

    let functions = printArray printA printName
    (BSR printName, [Function printName functions])

printArray :: Instruct -> String -> [Instruct]
printArray printA printName = [LABEL printName (LINK 1),
    LDL (-2),
    STL 1,
    LDC 91,
    TRAP 1,
    ResPoint (printName++"ResPoint") (LDL 1),
    LDC 0,
    Ssm.EQ,
    BRT (printName++"End"),
    LDL 1,
    LDH (-1),
    printA,
    LDL 1,
    LDH 0,
    LDC 0,
    Ssm.EQ,
    BRT (printName++"End"),
    LDC 44,
    TRAP 1,
    LDL 1,
    LDH 0,
    STL 1,
    LDResP (printName++"ResPoint"),
    STR PC,
    LABEL (printName++"End") (LDC 93),
    TRAP 1,
    UNLINK,
    RET]

genOverloadedOps :: Map String Op2Typed -> [SsmFunction]
genOverloadedOps ops | Map.null ops  = []
genOverloadedOps ops = concatMap  (\(x,y) -> snd (genCompare x y)) l
    where l = Map.elems $ Prelude.foldr (Map.union . genOverloadedOp ) Map.empty (Map.elems ops)

genOverloadedOp ::  Op2Typed -> Map String (Op2,SPLType)
genOverloadedOp (Op2 op (Just (TypeBasic _ BasicInt _)) _) = Map.empty
genOverloadedOp (Op2 op (Just (TypeBasic _ BasicChar _)) _) = Map.empty
genOverloadedOp (Op2 op (Just (TypeBasic locA BasicBool locB))_ ) =
    let name = overloadedTypeName (op2String op) (TypeBasic locA BasicBool locB)
    in Map.singleton name (op, TypeBasic locA BasicBool locB)
genOverloadedOp (Op2 op (Just (TupleType locA (t1,t2) locB)) opLoc)  =
    let name = overloadedTypeName (op2String op) (TupleType locA (t1,t2) locB)
    in Map.singleton name (op, TupleType locA (t1,t2) locB) `Map.union` genOverloadedOp (Op2 op (Just t1) opLoc)  `Map.union` genOverloadedOp (Op2 op (Just t2) opLoc) 
genOverloadedOp (Op2 op (Just (ArrayType locA a locB)) opLoc) = 
    let name = overloadedTypeName (op2String op) (ArrayType locA a locB)
    in Map.singleton name (op, ArrayType locA a locB) `Map.union` genOverloadedOp (Op2 op (Just a) opLoc)

genCompare :: Op2 -> SPLType -> (Instruct, [SsmFunction])
genCompare op (TypeBasic _ BasicBool _) = case op of
        Le  -> (Ssm.GT, [])
        Ge  -> (Ssm.LT, [])
        Leq -> (Ssm.GE, [])
        Geq -> (Ssm.NE, [])
        _   -> (op2Func op, [])
genCompare op TypeBasic {} = (op2Func op, [])
genCompare op (TupleType locA (t1,t2) locB) = do
    let opName = overloadedOpName op (TupleType locA (t1,t2) locB)
    let (t1Name, functionT1) = genCompare op t1
    let (t2Name, functionT2) = genCompare op t2
    
    let function = [LABEL opName (LINK 0),LDL (-3),LDH 0,LDL (-2),LDH 0,t1Name,STR RR,LDR RR
                                ,BRF (opName++"End"),LDL (-3),LDH (-1),LDL (-2),LDH (-1), t2Name, STR RR,
                                LABEL (opName++"End") UNLINK,RET]
    (BSR opName, [Function opName function])
genCompare op (ArrayType locA a locB) = do
    let opName = overloadedOpName op (ArrayType locA a locB)
    let (opExecA, functions') = genCompare op a
    (BSR opName,[Function opName (compArray op opExecA opName)])

dualityOP Ge = Geq 
dualityOP Le = Le 
dualityOP x = x

compArray :: Op2 -> Instruct -> String -> [Instruct]
compArray op compareA compName | op == Eq || op == Neq = 
    [LABEL compName (LINK 2),
    LDL (-3),
    STL 1,
    LDL (-2),
    STL 2,
    ResPoint (compName++"ResPoint") (COMMENT (LDL 1) "End of first list?"), 
    LDC 0,
    Ssm.EQ,
    COMMENT (LDL 2) "End of sec list?", 
    LDC 0,
    Ssm.EQ,
    COMMENT Ssm.OR "Any list (or both) Empty?",
    STR RR,
    LDR RR,
    BRT (compName++"End"),
    LDL 1,
    LDH (-1),
    LDL 2,
    LDH (-1),
    compareA,
    STR RR,
    LDR RR,
    BRF (compName++"End"),
    LDL 1,
    LDH 0,
    STL 1,
    LDL 2,
    LDH 0,
    STL 2,
    LDResP (compName++"ResPoint"),
    STR PC,
    LABEL (compName++"End") UNLINK,
    RET]
compArray op compareA compName  = 
    [LABEL compName (LINK 4),
    LDL (-3),
    STL 1,
    LDL (-2),
    STL 2,
    ResPoint (compName++"ResPoint") (COMMENT (LDL 1) "End of first list?"),
    LDC 0,
    Ssm.EQ,
    STL 3,
    COMMENT (LDL 2) "End of sec list?",
    LDC 0,
    Ssm.EQ,
    STL 4,
    LDL 3,
    LDL 4,
    Ssm.OR,
    BRT (compName++"Ret"),
    LDL 1,
    LDH (-1),
    LDL 2,
    LDH (-1),
    compareA,
    STR RR,
    LDR RR,
    if op == Geq || op == Ge then BRF (compName++"End") else BRT (compName++"End"),
    LDL 1,
    LDH 0,
    STL 1, 
    LDL 2,
    LDH 0,
    STL 2, 
    LDResP (compName++"ResPoint"),
    STR PC,
    LABEL (compName++"Ret") (if op == Geq || op == Leq then LDC (-1) else LDC 0),
    STR RR,
    LDL 3,
    LDL 4,
    Ssm.AND,
    BRT (compName++"End"),
    LDC (defFromOp op),
    STR RR,
    LDL 3,
    LDC (-1),
    Ssm.EQ,
    BRT (compName++"End"),
    LDR RR,
    NOT,
    STR RR,
    --End of comparison
    LABEL (compName++"End") UNLINK,
    RET]

defFromOp Le = -1
defFromOp Leq = -1
defFromOp Geq = 0
defFromOp Ge = 0


openBracket c  = LDC 40:TRAP 1:c
closeBracket c  = LDC 41:TRAP 1:c

openSqBracket c = LDC 91:TRAP 1:c
closeSqBracket c = LDC 93:TRAP 1:c

comma c = LDC 44:TRAP 1:c

typeToName :: SPLType -> String 
typeToName (TypeBasic _ x _) = pp x
typeToName (TupleType _ (t1,t2) _) = "Tuple" ++ typeToName t1 ++ typeToName t2
typeToName (ArrayType _ a1 _) = "Array"++ typeToName a1
typeToName (FunType arg f) = "Func"
typeToName (Void _ _) = "Void"
typeToName x = trace ("Error we did not catch type "++ pp x) undefined 

op2Func :: Op2 -> Instruct
op2Func Le  = Ssm.LT
op2Func Ge  = Ssm.GT
op2Func Leq = Ssm.LE
op2Func Geq = Ssm.GE
op2Func Eq  = Ssm.EQ
op2Func Neq = Ssm.NE

op2String :: Op2 -> String
op2String Le  = "lt"
op2String Ge  = "gt"
op2String Leq = "le"
op2String Geq = "ge"
op2String Eq  = "eq"
op2String Neq = "ne"

-- ==================== Helper functions ====================
combineResult :: Gen ([a], GenEnv) -> (GenEnv -> Gen ([a], GenEnv)) -> Gen ([a], GenEnv)
combineResult a b = do
    (resA, env) <- a
    (resB, env') <- b env
    return (resA++resB, env')

insertLabel :: String -> [Instruct] -> [Instruct]
insertLabel label (x:xs) = LABEL label x:xs

isVoidFun :: SPLType -> Bool
isVoidFun x = last (getArgsTypes x) `eqType` Void defaultLoc defaultLoc

insertComment :: String -> Gen ([Instruct], GenEnv) -> Gen ([Instruct], GenEnv)
insertComment comment gen = BI.first f <$> gen
    where f (x:xs) = COMMENT x comment:xs

-- ==================== Environment ====================
constructEnv :: GenEnv -> SPLType -> [IDLoc] -> [VarDecl] -> GenEnv
constructEnv env fType xs ys = Map.fromList decls `Map.union` Map.fromList args `Map.union` env
    where
        args = zipWith3 (\ id loc typ -> (id, L loc typ)) xs [(negate (length xs)-1 )..] (init $ getArgsTypes fType)
        decls = zipWith (\(VarDeclType t id e) b -> (id, L b t) ) ys [1..]

-- ==================== Instructions ====================
loadAddress :: Mem -> [Instruct] 
loadAddress (L x _) = [LDLA x]
loadAddress (G x t) = case x of
    0 -> load (R R5)
    _ -> load (R R5)++[LDC x, ADD]
loadAddress (R r)      = [LDR r]

load :: Mem -> [Instruct] 
load (L x _) = [LDL x]
load (G x t) = load (R R5)++[LDA x]
load (R r)      = [LDR r]

store :: Mem -> Instruct
store (L x _) = STL x
store (G x _) = STL x
store (R r)     = STR r

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

-- ==================== Main ====================
main :: IO ()
main = do
      file <- readFile "../SPL_test_code/test1.spl"
      case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
            Right(_, _, spl) ->
                case runGen $ genSPL spl of
                    (Right result,_) -> do
                                let output = pp result
                                writeFile "../generated_ssm/gen.ssm" output
                    (Left x,_) -> putStr $ "ERROR:\n" ++ show x ++ "\n" ++ showPlaceOfError file x
            Left x -> putStr $ "\nError:\n" ++ show x ++ "\n" ++ showPlaceOfError file x


mainGenTest1 :: IO ()
mainGenTest1  = do
      file <- readFile  "../SPL_test_code/test1.spl"
      case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
            Right(_, _, spl) -> do
                let res = runGen (genSPL spl)
                let (Right result,_) = res
                print result
                let output = pp result
                writeFile "../generated_ssm/gen.ssm" output
            Left x -> putStr $ "\nError:\n" ++ show x ++ "\n" ++ showPlaceOfError file x

mainGen :: String -> IO ()
mainGen filename = do
      file <- readFile  ("../SPL_test_code/" ++ filename)
      case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
            Right(_, _, spl) ->
                case runGen $ genSPL spl of
                    (Right result,_) -> do
                                let output = pp $ resPoints result
                                writeFile "../generated_ssm/gen.ssm" output
                    (Left x,_) -> putStr $ "ERROR:\n" ++ show x ++ "\n" ++ showError file x
            Left x -> putStr $ "\nError:\n" ++ showError file x