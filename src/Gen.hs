{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Gen where

import AST
import Error
import Parser
import MutRec
import TImisc
import TI
import SSM

import Data.Char
import Data.List ( intercalate, isPrefixOf )
import Data.Bifunctor as BI
import Data.Set as Set
import Data.Map as Map
import Data.Either

import Control.Monad.Except
import Control.Monad.State
import Control.Applicative

import Debug.Trace

-- ===== Types ====
data Mem =
    G Int SPLType | -- Global
    L Int SPLType | -- Local
    R Register              -- Global Pointer
    deriving (Show, Eq)

--               Ifs, Global, Overloaded functions, overloaded Op2s
type GenState = (Int, Int, (Map String Op2Typed, Map String FunCall))
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
insertOp2 (Op2 op (Just (FunType locF1 args t' locF2)) loc ) = do
    let t = head args
    (ifS, globalS, (ops, funcCalls)) <- get
    put (ifS, globalS, (Map.insert (overloadedOpName op t) (Op2 op (Just t) loc) ops, funcCalls))
insertOp2 (Op2 op (Just t) loc) = do
    (ifS, globalS, (ops, funcCalls)) <- get
    put (ifS, globalS, (Map.insert (overloadedOpName op t) (Op2 op (Just t) loc) ops, funcCalls))

insertFunCall :: FunCall -> Gen ()
insertFunCall (FunCall locF (ID locA id locB) args locF'(Just (FunType locF1 t t' locF2))) = do
    (ifS, globalS, (ops, funcCalls)) <- get
    let f = Map.insert (overloadedTypeName id (head t)) (FunCall locF (ID locA id locB) [] locF' (Just $ FunType locF1 t t' locF2)) funcCalls
    put (ifS, globalS, (ops, f))

-- ===== Generation =====
genSPL :: SPL -> Map String Op2Typed -> Map String FunCall -> Gen SSM
genSPL spl ops funcs = do
    let (globals, functions, mainDecl) = sortSPL spl
    (assemblyGlobals, env) <- genGlobals globals Map.empty
    (assemblyFunctions, env') <- genFunDecls functions env
    case mainDecl of
        Nothing -> throwError $ Error defaultLoc "No main without arguments detected"
        Just main -> do
            (assemblyMain, _) <- genFunDecl main env'
            (_, _, (overloadedOps,overloadedFuns)) <- get 
            let opsTI = Map.map adjustType ops
            return $ 
                SSM assemblyGlobals $
                    assemblyFunctions ++
                    genOverloadedOps True opsTI ++
                    genOverloadedOps False (overloadedOps Map.\\ opsTI) ++
                    -- genOverloadedFuns (overloadedFuns `Map.union` Map.map adjustFuncType funcs) ++ 
                    genOverloadedFuns True funcs ++ 
                    genOverloadedFuns False (overloadedFuns Map.\\ funcs) ++
                    [assemblyMain]
    where
        adjustType (Op2 op (Just  (FunType _ xs t _)) loc ) = Op2 op (Just $ head xs) loc
        -- adjustFuncType (FunCall locA id exp locB (Just (FunType _ (x:xs) _ _))) = FunCall locA id exp locB (Just x)


genGlobals :: [VarDecl] -> GenEnv -> Gen ([SsmGlobal], GenEnv)
genGlobals [] env = return ([],env)
genGlobals (g:gs) env = do
    (g', env') <- genVarDecl g [] GlobalScopeVar env
    (res, env'') <- genGlobals gs env'
    return (SSM.Global g':res, env'')

genVarDecls :: [VarDecl] -> [Instruct] -> Scope -> GenEnv -> Gen ([Instruct], GenEnv)
genVarDecls [] c _ env = return (c,  env)
genVarDecls (x:xs) c s env = do
    combineResult (genVarDecl x [] s env) (genVarDecls xs c s)

genVarDecl :: VarDecl -> [Instruct] -> Scope -> GenEnv -> Gen ([Instruct], GenEnv)
genVarDecl (VarDeclType t id e) c GlobalScopeVar env = do
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
    -- env' <- catchError ( constructEnv env fType [] vDecls) (const $ throwError (Error defaultLoc ("In main")))
    env' <- constructEnv env fType [] vDecls

    (res,env'') <- combineResult (genVarDecls vDecls [] LocalScope env') (genStmts False stmts [HALT] (ID locA "main" locB))

    return (Function "main" (LABEL "main" (LINK (length vDecls)):res), env'')
genFunDecl (FunDecl (ID locA name locB) args (Just fType) vDecls stmts) env = do
    resetIf
    env' <- constructEnv env fType args vDecls
    -- trace (name ++ " type: " ++ pp fType ++ " " ++ pp args ++ " " ++ show env') $ return () 
    (res, env'') <- combineResult
                        (genVarDecls vDecls [] LocalScope env')
                        (genStmts False stmts (genReturn fType name []) (ID locA name locB))
    
    return (Function name (LABEL name (LINK (length vDecls)):res), env'')
genFunDecl (FunDecl (ID locA "main" locB) _ _ _ _) _ = 
    throwError $ ErrorD (DLoc locA locB) "main function can't have arguments, return objects etc."

genReturn :: SPLType -> String -> [Instruct] -> [Instruct]
genReturn fType fName c | isVoidFun fType = LABEL (fName++"End") UNLINK:RET:c
genReturn fType fName c = LABEL (fName++"End") (STR RR):UNLINK:RET:c

genStmts :: Bool -> [Stmt] -> [Instruct] -> IDLoc -> GenEnv -> Gen ([Instruct], GenEnv)
genStmts recCall [] c id env = return (c, env)
-- The following two are here and not in genStmt because here we know if we need a continuation for something after the if stmt.
genStmts recCall ((StmtIf e stmts Nothing loc):xs) c id env = do
    let (ID _ fname _) = id
    (th, _, contin) <- newIf fname

    (ifStmt, env') <- combineResult (genExp e [BRF contin] env) (genStmts True stmts [] id)
    
    (rest, env'') <- genStmts True xs c id env'
    let rest' = insertLabel contin rest

    return $ if Prelude.null xs 
            then (ifStmt, env')
            else (ifStmt ++ rest', env'')
genStmts recCall ((StmtIf e stmts (Just els) loc):xs) c id env = do
    let (ID _ fname _) = id
    (th, _, contin) <- newIf fname

    let elseBranchEnd = if Prelude.null xs then [BRA (fname++"End")] else [BRA contin]

    (elseStmt, env') <- combineResult (genExp e [BRT th] env) (genStmts True els [] id)
    let elseStmt' = elseStmt ++ elseBranchEnd

    (ifElseStmt, env'') <- genStmts True stmts [] id env'
    -- if Prelude.null ifElseStmt then traceM (red ++ " ifElseStmt is empty! \n"++pp e ++ "\n" ++ pp loc ++ reset) else return ()
    let ifElseStmt' = insertLabel th ifElseStmt

    (rest, env''') <- genStmts True xs c id env''
    let rest' = insertLabel contin rest

    case (Prelude.null stmts, Prelude.null els, Prelude.null xs) of
        (True, True, True) -> return (c, env'')
        (False, True, True) -> return (elseStmt'++ifElseStmt'++c, env'')
        (True, False, True) -> return (elseStmt'++insertLabel th [NOP]++c, env'') 
        (True, True, False) -> return (rest, env''')
        (False, False, True) -> return (elseStmt'++ifElseStmt'++c, env'')
        (True, False, False) -> return (elseStmt'++insertLabel th [NOP]++rest', env''')
        (False, True, False) -> return (elseStmt'++ifElseStmt'++rest', env''')
        (False, False, False) -> return (elseStmt'++ifElseStmt'++rest', env''')

    -- return $ if Prelude.null xs 
    --             then (elseStmt++ifElseStmt'++c, env'') 
    --             else (elseStmt++ifElseStmt'++rest', env''')
genStmts recCall ((StmtWhile e stmts loc):xs) c id env = do
    let (ID _ fname _) = id
    whileName <- newWhile fname
    let whileEnd = whileName++"End"
    let fEnd = fname++"End"
    (cond, envCond) <- genExp e [] env
    (stmt, envStmt) <- genStmts True stmts [] id env
    (rst, envRst) <- genStmts True xs c id envStmt
    return $ if Prelude.null xs
        then (insertLabel whileName cond ++ [BRF fEnd] ++ stmt ++ BRA whileName:c, envStmt)
        else (insertLabel whileName cond ++ [BRF whileEnd] ++ stmt ++ BRA whileName :insertLabel whileEnd rst, envRst)
genStmts recCall [StmtReturn exp loc] c id env | not recCall =
    case exp of
        Nothing -> return (c, env)
        Just e -> genExp e c env
genStmts recCall (x:xs) c id env = do
    combineResult (genStmt x [] id env) (genStmts True xs c id) 

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
genFuncCall (FunCall locF (ID locA "print" locB) args locF' (Just (FunType locF1 (TypeBasic locA' t locB':xs) t' locF2))) c env =
    case t of
        BasicInt  -> genExps args (TRAP 0:c) env
        BasicChar -> genExps args (TRAP 1:c) env
        BasicBool -> do
            let printName = overloadedTypeName "print" (TypeBasic locA' t locB')
            insertFunCall (FunCall locF (ID locA "print" locB) args locF' (Just (FunType locF1 (TypeBasic locA' t locB':xs) t' locF2)))
            genExps args (BSR printName:AJS (-1):c) env
-- genFuncCall (FunCall (ID locA "print" locB) args (Just (FunType (ArrayType locA' (IdType id) locB') t'))) c env = do
--     let printName = "_printPolyEmptyList"
--     genExps args (COMMENT (LDC 91) "_printPolyEmptyList":TRAP 1:LDC 93:TRAP 1:c) env
genFuncCall (FunCall locF (ID locA "print" locB) args locF' (Just (FunType locF1 t t' locF2))) c env = do
    let printName = overloadedTypeName "print" (head t)
    insertFunCall (FunCall locF (ID locA "print" locB) args locF' (Just (FunType locF1 t t' locF2)))
    genExps args (BSR printName:AJS (-1):c) env
genFuncCall (FunCall locF (ID _ "isEmpty" _) args locF' (Just fType)) c env = do
    genExps args (LDC 0:SSM.EQ:c) env
genFuncCall (FunCall locF id args locF' (Just fType)) c env | Map.member id env = do
    let memId = env ! id -- Allready checked by guard so ! allowed
    let c' = (if isVoidFun fType then c else LDR RR:c)
    let c'' = (if Prelude.null args then c' else AJS (negate $ length args):c')
    genExps args (load memId++JSR:c'') env
genFuncCall (FunCall locF id args locF' (Just fType)) c env = do
    let c' = (if isVoidFun fType then c else LDR RR:c)
    let c'' = (if Prelude.null args then c' else AJS (negate $ length args):c')
    genExps args (BSR (pp id):c'') env
genFuncCall x c env = trace ("GOING WRONG HERE\n"++pp x) $ return (c, env)

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
genExp (ExpFunCall funcall) c env =
    genFuncCall funcall c env
genExp (ExpOp2 _ e1 op e2 _) c env  = do
    (operator, env') <- genOp2Typed op c env
    (secondArg, env'') <- genExp e2 operator env'
    genExp e1 secondArg env''
genExp (ExpOp1 _ op e _) c env = case op of
    Neg -> genExp e (NEG:c) env
    Not -> genExp e (NOT:c) env
genExp (ExpFunction _ id _ _) c env = return  (LDResP (getID id):c, env)

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

genOp2Typed (Op2 op (Just (FunType _ (TypeBasic _ BasicBool _:xs) _ _)) _) c env = 
    case op of
        Le  -> return (SSM.GT:c,env)
        Ge  -> return (SSM.LT:c,env)
        Leq -> return (SSM.GE:c,env)
        Geq -> return (SSM.NE:c,env)
        _   -> return (op2Func op:c,env)
genOp2Typed (Op2 op (Just (FunType _ (ArrayType _ (IdType _) _:xs) _ _))_) c env =
    return (op2Func op:c,env)
genOp2Typed (Op2 op (Just (FunType _ (TypeBasic{}:xs) _ _))_) c env = 
    return (op2Func op:c,env)
genOp2Typed (Op2 op (Just (FunType locF1 t t' locF2)) loc) c env = do
    let func = overloadedOpName op (head t)
    insertOp2 (Op2 op (Just (FunType locF1 t t' locF2)) loc)
    return (BSR func:AJS (-2):LDR RR:c, env)

-- ==================== Overloading functions ====================
genOverloadedFuns :: Bool -> Map String FunCall -> [SsmFunction]
genOverloadedFuns b funcs = concatMap (snd . genPrint b) $ Map.elems (getOverloadedFuns b (Map.toList funcs))

getOverloadedFuns :: Bool -> [(String, FunCall)] -> Map String SPLType
getOverloadedFuns b [] = Map.empty
getOverloadedFuns b ((name, FunCall _ (ID _ "print" _) _ _ (Just (FunType locF1 t t' locF2))):xs) = 
    getOverloadedFun b "print" (head t) `Map.union` getOverloadedFuns b xs
-- getOverloadedFuns ((name, FunCall _ id _ _ (Just (FunType locF1 t t' locF2))):xs) | "_print" `isPrefixOf` (getID id)  = 
--     getOverloadedFun "print" (head t) `Map.union` getOverloadedFuns xs
getOverloadedFuns b ((_,x):_) = error ("ERROR: " ++ pp x)
     

getOverloadedFun :: Bool -> String -> SPLType -> Map String SPLType
getOverloadedFun b funcName (TypeBasic locA BasicBool locB) = 
    let name = overloadedTypeName funcName (TypeBasic locA BasicBool locB)
    in Map.singleton name (TypeBasic locA BasicBool locB)
getOverloadedFun b funcName (TypeBasic locA t locB) =
    if b 
    then 
        let name = overloadedTypeName funcName (TypeBasic locA t locB) 
        in Map.singleton name (TypeBasic locA t locB)
    else Map.empty
getOverloadedFun b funcName (TupleType locA (t1,t2) locB) = 
    let name = overloadedTypeName funcName (TupleType locA (t1,t2) locB) 
    in Map.singleton name (TupleType locA (t1,t2) locB) `Map.union` getOverloadedFun b funcName t1 `Map.union` getOverloadedFun b funcName t2
getOverloadedFun b funcName (ArrayType locA a locB) =
    let name = overloadedTypeName funcName (ArrayType locA a locB)
    in Map.singleton name (ArrayType locA a locB) `Map.union` getOverloadedFun b funcName a
getOverloadedFun b funcName t = trace ("Unexpected input in getOverloadedFun: "++funcName ++ " with type: " ++ pp t) Map.empty  

genPrint :: Bool -> SPLType -> (Instruct, [SsmFunction])
-- genPrint b (TypeBasic _ BasicInt _) = 

genPrint b (TypeBasic _ BasicBool _) = do
    let function = [LABEL "_printBool"  (LINK 0),LDL (-2),BRF "_printFalse",
                        LDC 101,LDC 117,LDC 114,LDC 84,
                            TRAP 1,TRAP 1,TRAP 1,TRAP 1,UNLINK,RET,
                        LABEL "_printFalse" (LDC 101),LDC 115,LDC 108,LDC 97,LDC 70,
                            TRAP 1,TRAP 1,TRAP 1,TRAP 1,TRAP 1,UNLINK,RET]
    (BSR "_printBool", [Function "_printBool" function])
genPrint b (TypeBasic locA t locB) = do
    let name = overloadedTypeName "print" (TypeBasic locA t locB) 
    if b 
        then do
            let printT = fst $ genPrint False (TypeBasic locA t locB)
            let function = [LABEL name (LINK 0),LDL (-2), printT, UNLINK, RET]
            (BSR name, [Function name function])
        else if t == BasicChar then (TRAP 1, []) else (TRAP 0, [])
    
genPrint b (TupleType locA (t1,t2) locB)  = do
    let printName = overloadedTypeName "print" (TupleType locA (t1,t2) locB)

    let (printT1, functionT1) = genPrint False t1 
    let (printT2, functionT1T2) = genPrint False t2 

    let function = LABEL printName (LINK 0): 
                        openBracket (LDL (-2):LDH 0:printT1: 
                        comma (LDL (-2):LDH (-1):printT2: 
                        closeBracket [UNLINK,RET]))

    (BSR printName, [Function printName function]) 
genPrint b (ArrayType _ (IdType _) loc) = do
    let printName  = "_printPolyEmptyList"

    let functions = printArray NOP printName
    (BSR printName, [Function printName functions]) 
genPrint b (ArrayType locA a locB) = do
    let printName  = overloadedTypeName "print" (ArrayType locA a locB)
    let (printA, functionT1) = genPrint False a

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
    SSM.EQ,
    BRT (printName++"End"),
    LDL 1,
    LDH (-1),
    printA,
    LDL 1,
    LDH 0,
    LDC 0,
    SSM.EQ,
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

genOverloadedOps :: Bool -> Map String Op2Typed -> [SsmFunction]
genOverloadedOps func ops | Map.null ops  = []
genOverloadedOps func ops = concatMap  (\(x,y) -> snd (genCompare x func y)) l
    where l = Map.elems $ Prelude.foldr (Map.union . genOverloadedOp func ) Map.empty (Map.elems ops)

genOverloadedOp :: Bool -> Op2Typed -> Map String (Op2,SPLType)
genOverloadedOp func (Op2 op (Just (TypeBasic locA BasicBool locB))_ ) =
    let name = overloadedTypeName (op2String op) (TypeBasic locA BasicBool locB)
    in Map.singleton name (op, TypeBasic locA BasicBool locB)
genOverloadedOp func (Op2 op (Just (TypeBasic locA t locB)) _) = 
    if func 
        then 
            let name = overloadedTypeName (op2String op) (TypeBasic locA t locB)
            in Map.singleton name (op, TypeBasic locA t locB)
        else Map.empty
genOverloadedOp func (Op2 op (Just (TupleType locA (t1,t2) locB)) opLoc)  =
    let name = overloadedTypeName (op2String op) (TupleType locA (t1,t2) locB)
    in Map.singleton name (op, TupleType locA (t1,t2) locB) `Map.union` genOverloadedOp func (Op2 op (Just t1) opLoc)  `Map.union` genOverloadedOp func (Op2 op (Just t2) opLoc) 
genOverloadedOp func (Op2 op (Just (ArrayType locA a locB)) opLoc) = 
    let name = overloadedTypeName (op2String op) (ArrayType locA a locB)
    in Map.singleton name (op, ArrayType locA a locB) `Map.union` genOverloadedOp func (Op2 op (Just a) opLoc)
genOverloadedOp _ op = error ("We are not handeling this case: "++ pp op)

genCompare :: Op2 -> Bool -> SPLType -> (Instruct, [SsmFunction])
genCompare op func (TypeBasic locA BasicBool locB) = do
    let opName = overloadedOpName op (TypeBasic locA BasicBool locB)
    if func 
        then do
            let comp = fst $ genCompare op False (TypeBasic locA BasicBool locB) 
            let function = [LABEL opName (LINK 0),LDL (-3),LDL (-2), comp, STR RR, UNLINK, RET]
            (BSR opName,  [Function opName function])
        else
            case op of
                Le  -> (SSM.GT, [])
                Ge  -> (SSM.LT, [])
                Leq -> (SSM.GE, [])
                Geq -> (SSM.NE, [])
                _   -> (op2Func op, [])
genCompare op func (TypeBasic locA t locB) = do
    let opName = overloadedOpName op (TypeBasic locA t locB)
    if func
        then do
            let comp = op2Func op
            let function = [LABEL opName (LINK 0),LDL (-3),LDL (-2), comp, STR RR, UNLINK, RET]
            (BSR opName, [Function opName function])
        else (op2Func op, [])
genCompare op func (TupleType locA (t1,t2) locB) = do
    let opName = overloadedOpName op (TupleType locA (t1,t2) locB)
    let (t1Name, functionT1) = genCompare op False t1
    let (t2Name, functionT2) = genCompare op False t2
    
    let function = [LABEL opName (LINK 0),LDL (-3),LDH 0,LDL (-2),LDH 0,t1Name,STR RR,LDR RR
                                ,BRF (opName++"End"),LDL (-3),LDH (-1),LDL (-2),LDH (-1), t2Name, STR RR,
                                LABEL (opName++"End") UNLINK,RET]
    (BSR opName,[Function opName function])
genCompare op func (ArrayType locA a locB) = do
    let opName = overloadedOpName op (ArrayType locA a locB)
    let (opExecA, functions') = genCompare op False a
    (BSR opName,[Function opName (compArray op opExecA opName)])

compArray :: Op2 -> Instruct -> String -> [Instruct]
compArray op compareA compName | op == Eq || op == Neq = 
    [LABEL compName (LINK 2),
    LDL (-3),
    STL 1,
    LDL (-2),
    STL 2,
    ResPoint (compName++"ResPoint") (COMMENT (LDL 1) "End of first list?"), 
    LDC 0,
    SSM.EQ,
    COMMENT (LDL 2) "End of sec list?", 
    LDC 0,
    SSM.EQ,
    COMMENT SSM.OR "Any list (or both) Empty?",
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
    SSM.EQ,
    STL 3,
    COMMENT (LDL 2) "End of sec list?",
    LDC 0,
    SSM.EQ,
    STL 4,
    LDL 3,
    LDL 4,
    SSM.OR,
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
    SSM.AND,
    BRT (compName++"End"),
    LDC (defFromOp op),
    STR RR,
    LDL 3,
    LDC (-1),
    SSM.EQ,
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

op2Func :: Op2 -> Instruct
op2Func Le  = SSM.LT
op2Func Ge  = SSM.GT
op2Func Leq = SSM.LE
op2Func Geq = SSM.GE
op2Func Eq  = SSM.EQ
op2Func Neq = SSM.NE

-- ==================== Helper functions ====================
combineResult :: Gen ([a], GenEnv) -> (GenEnv -> Gen ([a], GenEnv)) -> Gen ([a], GenEnv)
combineResult a b = do
    (resA, env) <- a
    (resB, env') <- b env
    return (resA++resB, env')

insertLabel :: String -> [Instruct] -> [Instruct]
insertLabel label (x:xs) = LABEL label x:xs

insertComment :: String -> Gen ([Instruct], GenEnv) -> Gen ([Instruct], GenEnv)
insertComment comment gen = BI.first f <$> gen
    where f (x:xs) = COMMENT x comment:xs

-- ==================== Environment ====================
constructEnv :: GenEnv -> SPLType -> [IDLoc] -> [VarDecl] -> Gen GenEnv
constructEnv env (FunType _ argsTypes retType _) xs ys = return $ Map.fromList decls `Map.union` Map.fromList args `Map.union` env
    where
        args = zipWith3 (\ id loc typ -> (id, L loc typ)) xs [(negate (length xs)-1 )..] argsTypes
        decls = zipWith (\(VarDeclType t id e) b -> (id, L b t) ) ys [1..]
constructEnv env t args _ = throwError $ Error defaultLoc ("Wtf is this: "++ pp t ++ " " ++ pp args)

-- ==================== Instructions ====================
loadAddress :: Mem -> [Instruct] 
loadAddress (L x _) = [LDLA x]
loadAddress (G x t) = case x of
    0 -> load (R R5)
    _ -> load (R R5)++[LDC x, ADD]
loadAddress (R r)   = [LDR r]

load :: Mem -> [Instruct] 
load (L x _) = [LDL x]
load (G x t) = load (R R5)++[LDA x]
load (R r)   = [LDR r]

store :: Mem -> Instruct
store (L x _) = STL x
store (G x _) = STL x
store (R r)   = STR r

-- ==================== Main ====================
gen :: SPL -> Map String Op2Typed -> Map String FunCall -> Either Error SSM
gen spl ops funcs = do
    case runGen (genSPL spl ops funcs) of
        (Right ssm, _) -> Right ssm
        (Left err, _) -> Left err 

-- tokenizeParserTIGen :: String -> SSM
tokenizeParserTIGen file = tokenizeParserTI file >>= (\(_,_,c,(ops, funcs)) -> gen c ops funcs) >>= resPointsMonad

main :: IO ()
main = do
    file <- readFile "../SPL_test_code/test1.spl"
    case tokenizeParserTIGen file of
        Right result -> do
                    let output = pp result
                    writeFile "../generated_ssm/gen.ssm" output
        Left x -> putStr $ "ERROR:\n" ++ show x ++ "\n" ++ showPlaceOfError file x

mainGenTest1 :: IO ()
mainGenTest1  = do
      file <- readFile  "../SPL_test_code/test1.spl"
      case tokenizeParserTI file of
            Right(_, _, spl, (ops, funcs)) -> do
                let res = runGen (genSPL spl ops funcs)
                let (Right result,_) = res
                print result
                let output = pp result
                writeFile "../generated_ssm/gen.ssm" output
            Left x -> putStr $ "\nError:\n" ++ show x ++ "\n" ++ showPlaceOfError file x

mainGen :: String -> IO ()
mainGen filename = do
      file <- readFile  ("../SPL_test_code/" ++ filename)
      case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
            Right(_, _, spl, (ops, funcs)) ->
                case runGen $ genSPL spl ops funcs of
                    (Right result,_) -> do
                                let output = pp $ resPoints result
                                writeFile "../SPL_test_code/ti-out.spl" (pp spl)
                                writeFile "../generated_ssm/gen.ssm" output
                    (Left x,_) -> putStr $ "ERROR:\n" ++ show x ++ "\n" ++ showError file x
            Left x -> putStr $ "\nError:\n" ++ showError file x
