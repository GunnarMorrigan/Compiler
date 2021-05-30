module TI where

import Error
import Lexer
import AST
import Parser
import ReturnGraph
import MutRec
import TImisc


import Data.Map as Map
import Data.Set as Set
import Data.Maybe
import Data.These
import Data.Bifunctor as BI ( Bifunctor(first) )
import Data.List hiding (find)

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Chronicle
import Control.Monad.State

import System.Exit
import System.Directory
import Debug.Trace


-- ===================== Type inference ============================
tiSPL :: SPL -> TI (Subst, TypeEnv, SPL)
tiSPL (SPL decls) = do
    stdEnv <- stdLib
    (s1, env', decls') <- tiDecls stdEnv decls
    return (s1, env', SPL decls')

tiDecls :: TypeEnv -> [Decl] -> TI (Subst, TypeEnv,[Decl])
tiDecls env [] = return (nullSubst, env, [])
tiDecls env (decl:decls) = do
            (s1, env', x) <- tiDecl env decl
            (s2, env'', xs) <- tiDecls env' decls
            let cs1 = s2 `composeSubst` s1
            return (cs1, env'', x:xs)

tiDecl :: TypeEnv -> Decl -> TI (Subst, TypeEnv, Decl)
tiDecl env (VarMain x) = do
    (s1, env, varDecl) <- tiVarDecl env x GlobalScope
    return (s1, env,VarMain varDecl)
tiDecl env (FuncMain x) = do
    (s1, env, funDecl) <- tiFunDecl env x
    return (s1, env, FuncMain funDecl)
tiDecl env (MutRec [func]) = do
    (s1, env, funDecl) <- tiFunDecl env func
    return (s1, env, FuncMain funDecl)
tiDecl env (MutRec funcs) = do
    fTypes <- getFuncTypes funcs
    env' <- insertMore env fTypes
    (s1, env'', decls) <- tiMutRecFunDecls env' funcs
    env''' <- generalizeFuncs env'' (Prelude.map (\(a,_,_) -> a) fTypes)
    return (s1, env''', MutRec decls)

tiVarDecls :: TypeEnv -> [VarDecl] -> Scope -> TI (Subst, TypeEnv, [VarDecl])
tiVarDecls env [] s = return (nullSubst, env, [])
tiVarDecls env (varDecl:varDecls) s = do
    (s1, env', varDecl') <- tiVarDecl env varDecl s
    (s2, env'', varDecls') <- tiVarDecls env' varDecls s
    return (s2 `composeSubst` s1, env'', varDecl':varDecls')

tiVarDecl :: TypeEnv -> VarDecl -> Scope -> TI (Subst, TypeEnv, VarDecl)
tiVarDecl (TypeEnv env) (VarDeclVar id e) s =
    case lookupKey id env of
        Just _ | builtin id -> 
            dictate (declaringStdFunction id) >>
            return (nullSubst, TypeEnv env, VarDeclVar id e)
        Just((scheme,s'),id') | s==s'-> dictate (doubleDef2 id id') >>
            return (nullSubst, TypeEnv env, VarDeclVar id e)
        _ -> do
            (s1, t1, e') <- tiExp (TypeEnv env) e
            let scheme = Scheme [] t1
            let env' = TypeEnv (Map.insert id (scheme,s) env)
            return (s1, apply s1 env', VarDeclType t1 id e')
tiVarDecl (TypeEnv env) (VarDeclType t id e) s =
    case lookupKey id env of
        Just _ | builtin id -> 
            dictate (declaringStdFunction id) >>
            return (nullSubst, TypeEnv env, VarDeclVar id e)
        Just((scheme,s'),id') | s==s'-> dictate (doubleDef2 id id') >>
            return (nullSubst, TypeEnv env, VarDeclType t id e)
        _ -> do
            (s1, t1, e') <- tiExp (TypeEnv env) e
            s2 <- mgu (apply s1 t) t1
            let cs1 = s2 `composeSubst` s1
            let scheme = Scheme [] t1
            let env' = TypeEnv (Map.insert id (scheme,s) env)
            return (cs1, apply cs1 env', VarDeclType t1 id e')

tiMutRecFunDecls :: TypeEnv -> [FunDecl] -> TI (Subst, TypeEnv, [FunDecl])
tiMutRecFunDecls env [] = return (nullSubst, env, [])
tiMutRecFunDecls (TypeEnv env) ((FunDecl funName args (Just funType) vars stmts):xs) = do
    let (argTypes, retType) = let a = getArgsTypes funType in (init a, last a)
    env' <- insertMore (TypeEnv env) (zip3 args argTypes (replicate (length args) GlobalScope)) -- With this function + args inserted

    (s1, env'', vars') <- tiVarDecls env' vars LocalScope

    (s2, t1, stmts') <- tiStmts env'' stmts

    let cs1 = s2 `composeSubst` s1

    let t1' = fromMaybe (Void defaultLoc defaultLoc) t1
    s3 <- mgu (apply cs1 t1') retType

    let cs2 = s3 `composeSubst` cs1

    (s4, env'', funDecls) <- tiMutRecFunDecls (apply cs2 (TypeEnv env)) xs

    let cs3 = s4 `composeSubst` cs2

    let funDecl = FunDecl funName args (Just $ apply cs3 funType) vars' stmts'

    return (cs3, apply cs3 env'', funDecl:funDecls)
tiMutRecFunDecls (TypeEnv env) ((FunDecl funName args Nothing vars stmts):xs) = do
    case Map.lookup funName env of
        Just (Scheme [] funType,GlobalScope) -> do

            let (argTypes, retType) = let a = getArgsTypes funType in (init a, last a)
            env' <- insertMore (TypeEnv env) (zip3 args argTypes (replicate (length args) ArgScope)) -- With this function + args inserted

            (s1, env'', vars') <- tiVarDecls env' vars LocalScope

            (s2,t1, stmts') <- tiStmts env'' stmts

            let cs1 = s2 `composeSubst` s1

            let t1' = fromMaybe (Void defaultLoc defaultLoc) t1
            s3 <- mgu (apply cs1 t1') retType

            let cs2 = s3 `composeSubst` cs1

            (s4, env''', funDecls') <- tiMutRecFunDecls (apply cs1 (TypeEnv env)) xs

            let cs3 = s4 `composeSubst` cs2

            let funDecl' = FunDecl funName args (Just $ apply cs3 funType) vars' stmts'

            return (cs3, apply cs2 env''', funDecl':funDecls')
        Just _ -> do undefined

        nothing ->
            dictate (ErrorD (getDLoc funName) "Function is mutual recursive and should therefore be in the type environment but it is not.") >>
            return (nullSubst, TypeEnv env, [])

tiFunDecl :: TypeEnv -> FunDecl -> TI (Subst, TypeEnv, FunDecl)
tiFunDecl env (FunDecl funName args funType vars stmts) |
    not $ isGoodScope GlobalScope funName env =
        dictate (applVarAsFunc funName) >>
        return (nullSubst, env, FunDecl funName args funType vars stmts)
tiFunDecl env (FunDecl funName args _ vars stmts) | pp funName == "main" =
    if not $ Prelude.null args
        then
            confess (ErrorD (getDLoc funName) "main should have zero arguments.")
        else do
            let fType = Void defaultLoc defaultLoc
            (s1, env', vars') <- tiVarDecls env vars LocalScope -- With this env + local varDecls inserted

            (s2, t1, stmts') <- tiStmts env' stmts

            let cs1 = s2 `composeSubst` s1
            let retType = fromMaybe (Void defaultLoc defaultLoc) t1
            s3 <- mgu fType retType

            let cs2 = s3 `composeSubst` cs1

            -- let funDecl = FunDecl funName args (Just fType) (apply cs2 vars') (apply cs2 stmts')
            let funDecl = FunDecl funName args (Just fType) vars' stmts'
            let finaleScheme = generalize env' fType

            (_, overloaded) <- monomorphize funDecl env'

            if  nullOL overloaded
                then
                    -- trace ("No 'poly' overloading in " ++ pp funName) $
                    return (cs2, TImisc.insert (apply cs2 env) funName finaleScheme GlobalScope, funDecl)
                else
                    confess (Error (getFstLoc funName) ("Some functions require overloaded built-ins (print, ==, <, >, etc) but the type for these functions is unkown.\n" 
                                                ++"It is thus impossible to create these for you."))
            
tiFunDecl env (FunDecl funName args (Just funType) vars stmts) = do
    let (argTypes, retType) = let a = getArgsTypes funType in (init a, last a)
    case length args `compare` length argTypes of
        LT ->
            dictate (funcCallLessArgs funName) >>
            return (nullSubst, env, FunDecl funName args (Just funType) vars stmts)
        GT ->
            dictate (funcCallMoreArgs funName) >>
            return (nullSubst, env, FunDecl funName args (Just funType) vars stmts)
        EQ -> do
            env' <- TImisc.insertID env funName funType GlobalScope -- With only this function inserted
            env'' <- insertMore env' (zip3 args argTypes (replicate (length args) ArgScope)) -- With this function + args inserted
            (s1, env''', vars') <- tiVarDecls env'' vars LocalScope -- With this function + args + local varDecls inserted

            (s2,t1, stmts') <- tiStmts env''' stmts

            let cs1 = s2 `composeSubst` s1

            let t1' = fromMaybe (Void defaultLoc defaultLoc) t1
            s3 <- mgu (apply cs1 t1') retType

            let cs2 = s3 `composeSubst` cs1

            let funType' = apply cs2 funType
            let funDecl = FunDecl funName args (Just funType') (apply cs2 vars') (apply cs2 stmts')

            (funDecl', overloaded) <- monomorphize funDecl env'''
            let (polyOp2, polyFunCall) = toListOL overloaded
            if  nullOL overloaded
                then
                    -- trace ("No 'poly' overloading in " ++ pp funName) $
                    -- let funcScheme = trace ("\n\nFree stuff in: " ++pp funName ++ "\n" ++ pp funType ++"\n" ++ pp (Set.toList $ ftv funType) ++ "\n\n" ++ pp (Set.toList $ ftv env)++ "\n\n") generalize env funType in
                    let funcScheme = generalize env funType in
                    return (cs2, TImisc.insert (apply cs2 env) funName funcScheme GlobalScope, funDecl')
                else
                    -- trace ("Poly overloading in " ++ pp funName {-- ++ "\n\n" ++ show polyOp2 ++ "\n\n" ++ show polyFunCall --}) $ 
                    do
                        let (args', fType', scheme) = overloadFunction args funType env polyOp2 polyFunCall
                        let FunDecl funName' _ (Just _) vars'' stmts'' = funDecl'
                        return (cs2, TImisc.insert (apply cs2 env) funName scheme GlobalScope, FunDecl funName' args' (Just fType') vars'' stmts'')
                        -- return (scheme, FunDecl funName' args' (Just fType') vars' stmts')
tiFunDecl env (FunDecl funName args Nothing vars stmts) = do
    argTypes <- replicateM (length args) newSPLVar
    retType <- newSPLVar

    let fType = if not (Prelude.null argTypes) then foldr1 FunType (argTypes ++ [retType]) else retType
    env' <- TImisc.insertID env funName fType GlobalScope -- With only this function inserted
    env'' <- insertMore env' (zip3 args argTypes (replicate (length args) ArgScope)) -- With this function + args inserted
    (s1, env''', vars') <- tiVarDecls env'' vars LocalScope -- With this function + args + local varDecls inserted

    (s2, t1, stmts') <- tiStmts env''' stmts

    let cs1 = s2 `composeSubst` s1
    let t1' = fromMaybe (Void defaultLoc defaultLoc) t1

    s3 <- mgu (apply cs1 t1') retType
    let cs2 = s3 `composeSubst` cs1

    -- let Just (Scheme [] t) = find funName env'''

    let funType = apply cs2 fType

    -- trace ("HIERZO "++ pp funName ++ "\n" ++ printEnv env''' ++ printSubst (Map.toList cs1) ++  pp funType ++ "\nEND") $ do
    let funDecl = FunDecl funName args (Just funType) (apply cs2 vars') (apply cs2 stmts')
    -- let funDecl = FunDecl funName args (Just funType) vars' stmts'


    (funDecl', overloaded) <- monomorphize funDecl env'''
    let (polyOp2, polyFunCall) = toListOL overloaded
    if  nullOL overloaded
        then
            -- trace ("No 'poly' overloading in " ++ pp funName) $
            -- let funcScheme = trace ("\n\nFree stuff in: " ++pp funName ++ "\n" ++ pp funType ++"\n" ++ pp (Set.toList $ ftv funType) ++ "\n\n" ++ pp (Set.toList $ ftv env)++ "\n\n") generalize env funType in
            let funcScheme = generalize env funType in
            return (cs2, TImisc.insert (apply cs2 env) funName funcScheme GlobalScope, funDecl')
        else
            -- trace ("Poly overloading in " ++ pp funName {-- ++ "\n\n" ++ show polyOp2 ++ "\n\n" ++ show polyFunCall --}) $ 
            do
                let (args', fType', scheme) = overloadFunction args funType env polyOp2 polyFunCall
                let FunDecl funName' _ (Just _) vars'' stmts'' = funDecl'
                return (cs2, TImisc.insert (apply cs2 env) funName scheme GlobalScope, FunDecl funName' args' (Just fType') vars'' stmts'')

tiStmts :: TypeEnv -> [Stmt] -> TI (Subst, Maybe SPLType, [Stmt])
tiStmts env [] = return (nullSubst,Nothing,[])
tiStmts env [e] = do
    (s1, t1, stmt') <- tiStmt env e
    return (s1, t1, [stmt'])
tiStmts env (e:es) = do
        (s1, t1, stmt') <- tiStmt env e
        (s2, retType, stmts') <- tiStmts (apply s1 env) es
        let cs1 = s2 `composeSubst` s1
        s3 <- mgu (apply cs1 t1) retType
        let cs2 = s3 `composeSubst` cs1
        return (cs2, retType, stmt':stmts')

tiStmt :: TypeEnv -> Stmt -> TI (Subst, Maybe SPLType, Stmt)
tiStmt env (StmtIf e stmts (Just els) loc) = do
    defType <- newSPLVar
    let def = (nullSubst, defType, e)

    (s1, conditionType, e') <- injectErrLoc def (tiExp env e) (getDLoc e)
    s2 <- injectErrLocMsg nullSubst (mgu conditionType (TypeBasic defaultLoc BasicBool defaultLoc)) (getDLoc e) ("Given condition does not have type Bool " ++ showLoc e)

    let cs1 = s2 `composeSubst` s1
    (s3, retIf, ifStmts) <- tiStmts (apply cs1 env) stmts

    let cs2 = s3 `composeSubst` cs1
    (s4, retElse, elseStmts) <- tiStmts (apply cs2 env) els

    let cs3 = s4 `composeSubst`cs2
    s5 <- mgu (apply cs3 retIf) (apply cs3 retElse)

    let cs4 = s5 `composeSubst` cs3
    return (cs4, apply cs4 retIf, StmtIf e' ifStmts (Just elseStmts) loc)
tiStmt env (StmtIf e stmts els loc) | els == Just [] || isNothing els = do
    defType <- newSPLVar
    let def = (nullSubst, defType, e)

    (s1, conditionType, e') <- injectErrLoc def (tiExp env e) (getDLoc e)
    s2 <- injectErrLocMsg nullSubst (mgu conditionType (TypeBasic defaultLoc BasicBool defaultLoc)) (getDLoc e) ("Given condition does not have type Bool " ++ showLoc e)

    let cs1 = s2 `composeSubst` s1
    (s3, t2, stmts') <- tiStmts (apply cs1 env) stmts

    let cs2 = s3 `composeSubst` cs1
    return (cs2, apply cs2 t2, StmtIf e' stmts' els loc)
tiStmt env (StmtWhile e stmts loc) = do
    defType <- newSPLVar
    let def = (nullSubst, defType, e)

    (s1, conditionType, e') <- injectErrLoc def (tiExp env e) (getDLoc e)
    s2 <- injectErrLocMsg nullSubst (mgu conditionType (TypeBasic defaultLoc BasicBool defaultLoc)) (getDLoc e) ("Given condition does not have type Bool " ++ showLoc e)
    let cs1 = s2 `composeSubst` s1

    (s3, t3, stmts') <- tiStmts (apply cs1 env) stmts
    let cs2 = s3 `composeSubst` cs1

    return (cs2, apply cs2 t3, StmtWhile e' stmts' loc)
tiStmt env (StmtFuncCall funCall loc) = do
    (s1, t, funCall',_) <- tiFunCall env False funCall
    return (s1, Nothing, StmtFuncCall  funCall' loc)

tiStmt env (StmtReturn Nothing (Loc line col)) =
    return (nullSubst, Just (Void (Loc line col) (Loc line (col+6))), StmtReturn Nothing (Loc line col))
tiStmt env (StmtReturn (Just e) loc) = do
    (s1, t1, e') <- tiExp env e
    return (s1, Just t1, StmtReturn (Just e') loc)

tiStmt (TypeEnv env) (StmtAssignVar id (Field []) e typ) =
    case Map.lookup id env of
    Just (scheme,s) | builtin id -> 
        dictate (assigningToStdFunction id) >>
        return (nullSubst, Nothing, StmtAssignVar id (Field []) e typ)
    Just (scheme,s) -> do 
        t <- instantiate scheme
        (s1, t1, e') <- tiExp (TypeEnv env) e
        s2 <- mgu (apply s1 t) t1
        let cs1 = s2 `composeSubst` s1
        return (cs1, Nothing, StmtAssignVar id (Field []) e' (Just t1))
    Nothing ->
        dictate (refBeforeDec "Variable:" id) >>
        return (nullSubst, Nothing, StmtAssignVar id (Field []) e typ)
tiStmt (TypeEnv env) (StmtAssignVar id (Field fields) e typ) = case Map.lookup id env of
    Just (scheme,s) | builtin id -> 
        dictate (assigningToStdFunction id) >>
        return (nullSubst, Nothing, StmtAssignVar id (Field fields) e typ)
    Nothing ->
        dictate (refBeforeDec "Variable:" id) >>
        return (nullSubst, Nothing, StmtAssignVar id (Field fields) e typ)
    Just (scheme,s) -> do
        t <- instantiate scheme
        (s1, t1, e') <- tiExp (TypeEnv env) e
        (s2, t', ret) <- getType t fields
        let cs1 = s2 `composeSubst` s1
        s3 <- mgu (apply cs1 ret) t1
        let cs2 = s3 `composeSubst` cs1
        s4 <- mgu (apply cs2 t') t
        let cs3 = s4 `composeSubst` cs2
        return (cs3, Nothing, StmtAssignVar id (Field fields) e' (Just $ apply cs3 ret))

typeCheckExps :: IDLoc -> Bool -> TypeEnv -> Subst -> [Exp] -> [Op2Typed] -> [FunCall] -> [SPLType] -> TI (Subst, [Exp],Overloaded)
typeCheckExps _ _ env s [] _ _ [] = return (s, [], emptyOL)
typeCheckExps id _ env s exps ops funcs argTypes | length exps < length argTypes && length exps + length ops + length funcs > length argTypes =
    dictate (funcCallMoreArgs id) >>
    -- dictate (stupidError ("Error\n" ++pp id ++ "\n" ++ pp exps ++ "\nhere on 529")) >>
    return (s, [], emptyOL)
typeCheckExps id _ env s exps ops funcs argTypes | length exps + length ops + length funcs < length argTypes =
    dictate (funcCallLessArgs id)
    >> return (s, [], emptyOL)
typeCheckExps id monomorph env s (e:es) ops funcs (t:ts) = do
    defType <- newSPLVar
    let def = (nullSubst, defType, e)

    (s1, t1, e') <- injectErrMsgAddition def (tiExp env e) (getDLoc e) "typeCheckExps"
    let cs1 = s1 `composeSubst` s
    -- s2 <- injectErrLocMsg nullSubst (mgu (apply cs1 t) t1) (getDLoc e) ("Argument '"++ pp e ++ "' should have type "++ pp t)
    -- s2 <- trace ("Argument '"++ pp e ++ "' should have type "++ pp t ++ " and has "++ pp t1) $  injectErrLoc nullSubst (mgu (apply cs1 t) t1) (getDLoc e)
    s2 <- injectErrLoc nullSubst (mgu (apply cs1 t) t1) (getDLoc e)
    let cs2 = s2 `composeSubst` cs1
    (s3, es', ol) <- typeCheckExps id monomorph (apply cs1 env) cs2 es ops funcs ts
    return (s3 `composeSubst` cs2 , e':es', ol)

typeCheckExps id monomorph env s [] (op:ops) funcs (t:ts) = do
    let (Op2 op' (Just opType) loc) = apply s op
    s1 <- mgu t opType
    let cs1 = s1 `composeSubst` s
    let opType1 = apply cs1 opType
    let FunType firstArgType _ = opType1

    -- trace ("typeCheckExps op: " ++ pp op' ++" mono: "++ show monomorph ++ " " ++pp id ++ " \n" ++ pp opType ++ " \n" ++ pp opType1  ++ "\n" ++ pp (apply cs1 opType1) ++ "\n" ++ pp (apply cs1 t) ) $ 
    if containsIDType opType1
        then
            if monomorph
                then do
                    let name = idLocCreator $ overloadedOpName op' firstArgType
                    let exp = ExpFunction defaultLoc name defaultLoc (Just opType1)
                    (s2,es',ol1) <- typeCheckExps id monomorph env cs1 [] ops funcs ts
                    let ol2 = singletonOLOp (Op2 op' (Just opType1) loc)
                    let ol3 = ol2 `unionOL` ol1
                    return (s2 `composeSubst` cs1, exp:es', ol3)
                else do
                    let name = idLocCreator $ overloadedOpName op' firstArgType
                    (s2,es',ol1) <- typeCheckExps id monomorph env cs1 [] ops funcs ts
                    let ol2 = singletonOLOp (Op2 op' (Just opType1) loc)

                    return (s2 `composeSubst` cs1, es', ol2 `unionOL` ol1)
        else do
                -- Everything about the opType1 is known, we can thus insert safely.
                insertOp2TI (Op2 op' (Just opType1) loc)
                let name = overloadedOpName op' firstArgType
                let exp = ExpFunction defaultLoc (idLocCreator name) defaultLoc (Just opType1)
                (s2,es', ol) <- typeCheckExps id monomorph env cs1 [] ops funcs ts
                return (s2 `composeSubst` cs1, exp:es', ol)

typeCheckExps id monomorph env s [] [] (func:funcs) (t:ts) = do
    let (FunCall (ID locA id' locB) es (Just funcType)) = apply s func
    s1 <- mgu t funcType
    let cs1 = s1 `composeSubst` s
    let funcType' = apply cs1 t
    let FunType firstArgType _ = funcType'

    -- trace ("typeCheckExps func: "++ id' ++ " mono: "++ show monomorph ++ " " ++pp id ++ " \n"++ pp funcType ++ "\n" ++ pp funcType' ++ "\n" ++ pp t ++ "\n" ++ pp (apply cs1 t) ) $
    if containsIDType funcType'
    then
        if monomorph
            then do
                let name = ID locA (overloadedTypeName "print" firstArgType) locB
                let exp = ExpFunction defaultLoc name defaultLoc (Just funcType')
                (s2,es',ol) <- typeCheckExps id monomorph env cs1 [] [] funcs ts
                let overloaded = singletonOLFun (FunCall name es (Just  funcType'))
                return (s2 `composeSubst` cs1, exp:es', overloaded `unionOL` ol)
            else do
                let name = ID locA (overloadedTypeName "print" firstArgType) locB
                -- let exp = ExpFunction defaultLoc name defaultLoc (Just funcType')
                (s2,es',ol) <- typeCheckExps id monomorph env cs1 [] [] funcs ts
                let overloaded = singletonOLFun (FunCall name es (Just  funcType'))
                return (s2 `composeSubst` cs1, es', overloaded `unionOL` ol)
    else do
        -- Everything about the FunCall is known, we can thus insert safely.
        insertFunCallTI (FunCall (ID locA "print" locB) es (Just funcType'))
        let name = overloadedTypeName "print" firstArgType
        let exp = ExpFunction defaultLoc (idLocCreator name) defaultLoc (Just funcType')
        (s2,es',ol) <- typeCheckExps id monomorph env cs1 [] [] funcs ts
        return (s2 `composeSubst` cs1, exp:es',ol)

tiExpsList :: TypeEnv -> [Exp] -> TI (Subst, SPLType, Exp)
tiExpsList env [e] = do
    (s1, t1, e') <- tiExp env e
    let arrayType = let (DLoc locA locB) = getDLoc t1 in ArrayType locA t1 locB
    let opType = Op2 Con (Just $ FunType t1 (FunType arrayType arrayType))
    let (DLoc locA locB) = getDLoc e
    return (s1, t1, ExpOp2 locA e' (opType locA) (ExpEmptyList locA locB) locB)
tiExpsList env (e:es) = do
    (s1, t1, e' ) <- tiExp env e
    (s2, t2, es') <- tiExpsList (apply s1 env) es
    let cs1 = s2 `composeSubst` s1
    s3 <- injectErrLoc nullSubst (mgu (apply cs1 t1) t2) (getDLoc e)

    let cs2 = s3 `composeSubst` cs1

    let arrayType = ArrayType (getFstLoc t2) t2 (getSndLoc t2)
    let opType = Op2 Con (Just $ FunType t1 (FunType arrayType arrayType))

    return (cs2, t2, ExpOp2 (getFstLoc e) e' (opType (getFstLoc e)) es' (getSndLoc e))

tiExp :: TypeEnv -> Exp -> TI (Subst, SPLType, Exp)
tiExp (TypeEnv env) (ExpId id (Field [])) = do
    case Map.lookup id env of
        Just (scheme,_) -> do
            t <- instantiate scheme 
            return (nullSubst, t, ExpId id (Field []))
        Nothing -> do
            t <- newSPLVar
            dictate (refBeforeDec "Variable:" id) >> return (nullSubst, t, ExpId id (Field []))
tiExp (TypeEnv env) (ExpId id (Field fields)) = case Map.lookup id env of
    Just (Scheme [] t,s)  -> do
        (s1, t', ret) <- getType t fields
        return (s1, ret, ExpId id (Field fields))
    Nothing -> do
        t <- newSPLVar
        dictate (refBeforeDec "Variable: " id) >> return (nullSubst, t, ExpId id (Field fields))
tiExp _ (ExpInt locA i locB)  = return (nullSubst, TypeBasic  locA BasicInt locB, ExpInt locA i locB)
tiExp _ (ExpBool locA b locB) = return (nullSubst, TypeBasic locA BasicBool locB, ExpBool locA b locB)
tiExp _ (ExpChar locA c locB) = return (nullSubst, TypeBasic locA BasicChar locB, ExpChar locA c locB)
tiExp env (ExpBracket e) = do
    (s1, t1, e') <- tiExp env e
    return (s1, t1, ExpBracket e')
tiExp env (ExpList loc [] loc' _) =
    confess (ErrorD (DLoc loc loc') "Removed ExpList [] because lists as [1,2,3] are converted to 1:2:3:[]")
tiExp env (ExpEmptyList loc loc') = do
      tv <- newSPLVar
      return (nullSubst, ArrayType defaultLoc tv defaultLoc, ExpEmptyList loc loc')
tiExp env (ExpList locA es locB Nothing) = do
    (s1, t1, es') <- tiExpsList env es
    return (s1, ArrayType locA t1 locB, es')
tiExp env (ExpTuple locA (e1, e2) locB _) = do
    (s1, t1, e1') <- tiExp env e1
    (s2, t2, e2') <- tiExp (apply s1 env) e2
    let cs1 = s2 `composeSubst` s1
    return (cs1, apply cs1 (TupleType locA (t1,t2) locB), ExpTuple locA (e1', e2') locB (Just $ TupleType locA (t1,t2) locB) )

tiExp env (ExpOp2 locA e1 (Op2 op opTyp loc) e2 locB) = do
    defType <- newSPLVar
    let def = (nullSubst, defType, ExpOp2 locA e1 (Op2 op opTyp loc) e2 locB)

    (t1, t2, t3, opType) <- op2Type op (getDLoc e1) (getDLoc e2)
    (s1, t1', e1') <- injectErrLoc def (tiExp env e1) (getDLoc e1)

    s2 <- injectErrLoc nullSubst (mgu t1' (apply s1 t1)) (getDLoc e1)
    let cs1 = s2 `composeSubst` s1

    (s3, t2', e2') <- injectErrLoc def (tiExp (apply cs1 env) e2) (getDLoc e2)
    let cs2 = s3 `composeSubst` cs1

    s4 <- injectErrLoc nullSubst (mgu (apply cs2 t2') (apply cs2  t2)) (getDLoc e2)
    let cs3 = s4 `composeSubst` cs2

    let finalOpType = apply cs3 opType

    return (cs3, apply cs3 t3, ExpOp2 locA e1' (Op2 op (Just finalOpType) loc) e2' locB)

tiExp env (ExpOp1 locA op e locB) = case op of
    Neg -> do
        (s1, t1, e') <- tiExp env e
        s2 <- mgu t1 (TypeBasic (getFstLoc t1) BasicInt (getSndLoc t1))
        return (s2 `composeSubst` s1, t1, ExpOp1 locA op e' locB)
    Not -> do
        (s1, t1, e') <- tiExp env e
        s2 <- mgu t1 (TypeBasic (getFstLoc t1) BasicBool (getSndLoc t1))
        return (s2 `composeSubst` s1, t1, ExpOp1 locA op e' locB)
tiExp env (ExpFunCall locA funCall locB) = do
    (s1, t, funCall', _) <- tiFunCall env False funCall
    return (s1, t, ExpFunCall locA funCall' locB)



tiExp (TypeEnv env) (ExpFunction locA function locB Nothing) = do
    case Map.lookup function env of
        Just (Scheme lockedVars lockedT,_) -> do
            t' <- instantiate (Scheme lockedVars lockedT)
            return (nullSubst, t', ExpFunction locA function locB (Just t'))
        Nothing -> confess (Error defaultLoc  "Ohh fuck on 692")
tiExp (TypeEnv env) (ExpFunction locA function locB (Just t)) |
    "_" `isPrefixOf` pp function = do
    case Map.lookup function env of
        Just (Scheme lockedVars lockedT,_) -> do
            t' <- instantiate (Scheme lockedVars lockedT)
            return (nullSubst, t', ExpFunction locA function locB (Just t'))
        Nothing -> return (nullSubst, t, ExpFunction locA function locB (Just t))
    -- return (s1, t, ExpFunCall locA funCall' locB)

tiExp env x = confess (Error defaultLoc ("Unkown tiExp" ++ show x)) 

tiFunction :: TypeEnv -> Exp -> TI (Subst, SPLType, Exp)
tiFunction (TypeEnv env) (ExpFunction locA id locB _) =
    case Map.lookup id env of
        Just (scheme,_) -> do
            t <- instantiate scheme
            return (nullSubst, t, ExpFunction locA id locB (Just t))
        Nothing -> do
            t <- newSPLVar
            dictate (refBeforeDec "Function" id) >> return (nullSubst, t,ExpFunction locA id locB Nothing)

tiFunCall :: TypeEnv -> Bool -> FunCall -> TI (Subst, SPLType, FunCall,Overloaded)
tiFunCall (TypeEnv env) monomorph (FunCall id args _) =
    case Map.lookup id env of
        Just (OverScheme lockedvars lockedType lockedOps lockedFuncs,GlobalScope) -> do
            (t, ops, funcs) <- instantiateOver (OverScheme lockedvars lockedType lockedOps lockedFuncs)
            let argTypes = getArgsTypes t

            (s1, args',ol) <- typeCheckExps id monomorph (TypeEnv env) nullSubst args ops funcs (init argTypes)
            let returnType = last argTypes
            -- trace ("\nCall \n"++ pp id ++"\nWith type:\n"++ pp t ++ "\nops:\n" ++ pp ops++"\nfull type type:\n" ++ pp (apply s1 t)) $
            return (s1, apply s1 returnType, FunCall id args' (Just $ apply s1 t),ol)
        Just (scheme,GlobalScope) -> do
            t <- instantiate scheme
            let argTypes = getArgsTypes t
            (s1, args', ol) <- typeCheckExps id monomorph (TypeEnv env) nullSubst args [] [] (init argTypes)
            let returnType = last argTypes
            return (s1, apply s1 returnType, FunCall id args' (Just $ apply s1 t), ol)
        Just (scheme,_) -> do
            t <- newSPLVar
            dictate (applVarAsFunc id ) >> return (nullSubst, t, FunCall id args Nothing, emptyOL)
        Nothing -> do
            t <- newSPLVar
            dictate (refBeforeDec "Function:" id) >> return (nullSubst, t, FunCall id args Nothing, emptyOL)
        -- x -> confess (Error defaultLoc  ("Did not expect"++show x))




-- ===================== Monomorphization ============================
class Monomorphization a where
    monomorphize :: a -> TypeEnv -> TI (a, Overloaded)

instance Monomorphization a => Monomorphization [a] where
    monomorphize [] env = return ([],emptyOL)
    monomorphize (x:xs) env = do
        (a,b) <- monomorphize x env
        (as,b') <- monomorphize xs env
        return (a:as, b`unionOL`b')

instance Monomorphization FunDecl where
    monomorphize (FunDecl funName args fType vars stmts) env = do
        (vars', ol1) <- monomorphize vars  env
        (stmts', ol2) <- monomorphize stmts env
        return (FunDecl funName args fType vars' stmts', ol1 `unionOL` ol2)

instance Monomorphization Stmt where
    monomorphize (StmtIf e stmts (Just els) loc) env = do
        (e', ol1) <- monomorphize e env
        (stmts', ol2) <- monomorphize stmts env
        (els', ol3) <- monomorphize els env
        return (StmtIf e' stmts' (Just els') loc, ol1 `unionOL` ol2 `unionOL` ol3)
    monomorphize (StmtIf e stmts Nothing loc) env = do
        (e', ol1) <- monomorphize e env
        (stmts', ol2) <- monomorphize stmts env
        return (StmtIf e stmts Nothing loc, ol1 `unionOL` ol2)
    monomorphize (StmtWhile e stmts loc) env = do
        (e', ol1) <- monomorphize e env
        (stmts', ol2) <- monomorphize stmts env
        return (StmtWhile e' stmts' loc, ol1 `unionOL` ol2)
    monomorphize (StmtAssignVar id fields e t) env = do
        (e',ol1) <- monomorphize e env
        return (StmtAssignVar id fields e' t, ol1)
    monomorphize (StmtFuncCall funCall loc) env = do
        (funCall', ol1) <- monomorphize funCall env
        return (StmtFuncCall funCall' loc, ol1)
    monomorphize (StmtReturn (Just e) loc) env = do
        (e', ol1) <- monomorphize e env
        return (StmtReturn (Just e') loc, ol1)
    monomorphize x env = return (x, emptyOL)

instance Monomorphization VarDecl where
    monomorphize (VarDeclType t id e) env = do
        (e', ol1) <- monomorphize e env
        return (VarDeclType t id e', ol1)
    monomorphize x env = return (x, emptyOL)

instance Monomorphization Exp where
    monomorphize (ExpBracket e) env = do
        (e', ol1) <- monomorphize e env
        return (ExpBracket e', ol1)
    monomorphize (ExpOp1 locA op e locB) env = do
        (e', ol1) <- monomorphize e env
        return (ExpOp1 locA op e' locB, ol1)
    monomorphize (ExpList locA exps locB t) env = do
        (exps', ol1) <- monomorphize exps env
        return (ExpList locA exps' locB t, ol1)
    monomorphize (ExpTuple locA (e1, e2) locB t) env = do
        (e1', ol1) <- monomorphize e1 env
        (e2', ol2) <- monomorphize e2 env
        return (ExpTuple locA (e1', e2') locB t, ol1 `unionOL` ol2)
    monomorphize (ExpOp2 locA e1 (Op2 op (Just (FunType t t')) loc) e2 locB) env | containsIDType (FunType t t') = do
        let name = idLocCreator $ overloadedOpName op t
        (e1', ol1) <- monomorphize e1 env
        (e2', ol2) <- monomorphize e2 env
        let exp = ExpFunCall locA (FunCall name [e1',e2'] (Just (FunType t t'))) locB
        return (exp, singletonOLOp (Op2 op (Just (FunType t t')) loc) `unionOL` (ol1 `unionOL` ol2))
    monomorphize (ExpOp2 locA e1 (Op2 op (Just (FunType t t')) loc) e2 locB) env = do
        let name = idLocCreator $ overloadedOpName op t
        (e1', ol1) <- monomorphize e1 env
        (e2', ol2) <- monomorphize e2 env
        let exp = ExpOp2 locA e1' (Op2 op (Just (FunType t t')) loc) e2' locB
        return (exp,ol1 `unionOL` ol2)
    monomorphize (ExpFunCall locA funCall locB) env = do
        (funCall', ol1) <- monomorphize funCall env
        return (ExpFunCall locA funCall' locB, ol1)
    monomorphize x env = return (x, emptyOL)

instance Monomorphization FunCall where
    monomorphize (FunCall (ID idLocA "print" idLocB) args (Just (FunType t t'))) env | containsIDType (FunType t t') = do
        let name = idLocCreator $ overloadedTypeName "print" t
        (args', ol1) <- monomorphize args env
        return
            (FunCall name args' (Just (FunType t t')),
            singletonOLFun (FunCall name args' (Just (FunType t t'))) `unionOL` ol1)
    monomorphize (FunCall id args t) env | containsIDTypeMaybe t = do
        defT <- newSPLVar
        let def = (nullSubst, defT , FunCall id args t,emptyOL)

        (_,_,funcall,overloaded) <- tiFunCall env True (FunCall id args t)

        -- trace ( "\nMonomorphizing "++pp id++"\n"++show overloaded ++ "\nEND\n") $ 
        return (funcall, overloaded)
    monomorphize x env = return (x, emptyOL)



instance Monomorphization Op2Typed where
    monomorphize (Op2 op (Just (FunType t t')) loc) env | containsIDType (FunType t t') = do
        let name = idLocCreator $ overloadedOpName op t
        return (Op2 op (Just (FunType t t')) loc, singletonOLOp (Op2 op (Just (FunType t t')) loc))
    monomorphize x env = return (x, emptyOL)




-- ===================== Main Type Inference ============================
typeInference :: SPL -> Either Error (Subst, TypeEnv, SPL)
typeInference code = do
    case runTI (tiSPL code) of
        (That (s1, env, SPL code'), state) -> do
            -- cleanCode <- removeDeadCode (SPL $ removeMutRec code')
            let cleanCode = SPL $ removeMutRec code'
            let updatedCode = apply s1 cleanCode
            Right (s1, env, updatedCode)
        (These errs a, state) -> Left errs
        (This errs, state) -> Left errs


mainTIIO filename = do

    file <- readFile  ("../SPL_test_code/" ++ filename)
    case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
        Right (s1, env, code) -> do
            putStr $ pp code
            putStr $ "\nEnv:\n" ++ printEnv env
            putStr $ "\nSubst:\n" ++ printSubst (Map.toList s1)
        Left x -> putStr $ showError file x


-- eq = FunDecl (ID (Loc 6 1) "equal" (Loc 6 6)) [ID (Loc 6 7) "x" (Loc 6 8),ID (Loc 6 10) "y" (Loc 6 11)] Nothing [] [StmtReturn (Just (ExpOp2 (Loc 7 14) (ExpId (ID (Loc 7 12) "x" (Loc 7 13)) (Field [])) (Op2 Eq Nothing (Loc 7 14)) (ExpId (ID (Loc 7 17) "y" (Loc 7 18)) (Field [])) (Loc 7 16))) (Loc 7 5)]

-- tiObject = do
--     -- path <- getCurrentDirectory
--     -- print path
--     case runTI (tiFunDecl (TypeEnv Map.empty) eq) of
--         (That (s1, env, code),_) -> do
--             print code
--             putStr "\n\n"
--             putStr $ pp code
--             putStr $ "\nEnv:\n" ++ printEnv env
--             putStr $ "\nSubst:\n" ++ printSubst (Map.toList s1)
--         (This x,_) -> print x
--         (These x _,_) -> print x


mainTI filename = do
    -- path <- getCurrentDirectory
    -- print path
    file <- readFile  ("../SPL_test_code/" ++ filename)
    case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= rtga >>= typeInference of
        Right (s1, env, code) -> do
            writeFile "../SPL_test_code/ti-out.spl"$ pp code
            putStr $ "\nEnv:\n" ++ printEnv env
            putStr $ "\nSubst:\n" ++ printSubst (Map.toList s1)
        Left x -> putStr $ showError file x

