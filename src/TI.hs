module TI where

import Error
import Lexer
import AST
import Parser (mainSegments, tokeniseAndParse)
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
    (s1, env, varDecl) <- tiVarDecl env x GlobalScopeVar
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
    traceM (red ++ printEnv env'' ++ reset)
    env''' <- generalizeFuncs env'' (Prelude.map (\(a,_,_) -> a) fTypes)
    traceM (red ++ printEnv env''' ++ reset)
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
        Just((OverScheme lVars lT lOps lFuncs ,s'),id') -> do
            (s1, t1, e') <- tiExp (TypeEnv env) e
            s2 <- mgu (apply s1 t) t1
            let cs1 = s2 `composeSubst` s1
            let scheme = Scheme [] t1
            let env' = TypeEnv (Map.insert id (scheme,s) env)
            return (cs1, apply cs1 env', VarDeclType t1 id e')
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
    let FunType locF1 argTypes retType locF2 = funType
    env' <- insertMore (TypeEnv env) (zip3 args argTypes (replicate (length args) ArgScope)) -- With this function + args inserted

    (s1, env'', vars') <- tiVarDecls env' vars LocalScope

    (s2, t1, stmts') <- tiStmts env'' stmts

    let cs1 = s2 `composeSubst` s1

    let t1' = fromMaybe (Void defaultLoc defaultLoc) t1
    s3 <- mgu (apply cs1 t1') retType

    let cs2 = s3 `composeSubst` cs1

    (s4, env'', funDecls) <- tiMutRecFunDecls (apply cs2 (TypeEnv env)) xs

    let cs3 = s4 `composeSubst` cs2

    let funDecl = FunDecl funName args (Just $ apply cs2 funType) (apply cs2 vars') (apply cs2 stmts')

    let returnEnv = apply cs3 env''

    return (cs3, apply cs3 env'', funDecl:funDecls)
tiMutRecFunDecls (TypeEnv env) ((FunDecl funName args Nothing vars stmts):xs) = do
    case Map.lookup funName env of
        Just (Scheme [] funType,s) | isGlobalScope s ->  do

            let FunType locF1 argTypes retType locF2 = funType
            env' <- insertMore (TypeEnv env) (zip3 args argTypes (replicate (length args) ArgScope)) -- With this function + args inserted

            (s1, env'', vars') <- tiVarDecls env' vars LocalScope

            (s2,t1, stmts') <- tiStmts env'' stmts

            let cs1 = s2 `composeSubst` s1

            let t1' = fromMaybe (Void defaultLoc defaultLoc) t1
            s3 <- mgu (apply cs1 t1') retType

            let cs2 = s3 `composeSubst` cs1

            (s4, env''', funDecls') <- tiMutRecFunDecls (apply cs1 (TypeEnv env)) xs

            let cs3 = s4 `composeSubst` cs2

            let funtype' = apply cs3 funType

            -- let funDecl' = FunDecl funName args (Just funtype') (apply cs2 vars') (apply cs2 stmts')
            let funDecl' = FunDecl funName args (Just funtype') vars' stmts'

            return (cs3, apply cs3 env''', funDecl':funDecls')

        r ->
            dictate (ErrorD (getDLoc funName) ("Function is mutual recursive and should therefore be in the type environment but it is not." ++ show r)) >>
            return (nullSubst, TypeEnv env, [])

tiFunDecl :: TypeEnv -> FunDecl -> TI (Subst, TypeEnv, FunDecl)
tiFunDecl env (FunDecl funName args funType vars stmts) |
    not $ isGoodScope GlobalScopeFun funName env =
        dictate (applVarAsFunc funName) >>
        return (nullSubst, env, FunDecl funName args funType vars stmts)
tiFunDecl env (FunDecl funName args _ vars stmts) | pp funName == "main" =
    if not $ Prelude.null args
        then
            confess (ErrorD (getDLoc funName) "main should have zero arguments.")
        else do
            let fType = FunType (getFstLoc funName) [] (Void defaultLoc defaultLoc) (getSndLoc funName)
            (s1, env', vars') <- tiVarDecls env vars LocalScope -- With this env + local varDecls inserted

            (s2, t1, stmts') <- tiStmts env' stmts


            let cs1 = s2 `composeSubst` s1
            let retType = fromMaybe (Void defaultLoc defaultLoc) t1
            s3 <- mgu (Void defaultLoc defaultLoc) retType

            let cs2 = s3 `composeSubst` cs1

            let funDecl = FunDecl funName args (Just $ apply cs2 fType) (apply cs2 vars') (apply cs2 stmts')
            -- let funDecl = FunDecl funName args (Just fType) vars' stmts'
            let finaleScheme = generalize env' fType

            (_,s, overloaded) <- monomorphize funDecl env'

            if  nullOL overloaded
                then
                    -- trace ("No 'poly' overloading in " ++ pp funName) $
                    return (cs2, TImisc.insert (apply cs2 env) funName finaleScheme GlobalScopeFun, funDecl)
                else
                    confess (Error (getFstLoc funName) ("Some functions require overloaded built-ins (print, ==, <, >, etc) but the type for these functions is unkown.\n" 
                                                ++"It is thus impossible to create these for you."))

tiFunDecl env (FunDecl funName args (Just funType) vars stmts) = do
    let FunType locF1 argTypes retType locF2 = funType
    case length args `compare` length argTypes of
        LT ->
            dictate (funcCallLessArgs funName) >>
            return (nullSubst, env, FunDecl funName args (Just funType) vars stmts)
        GT ->
            dictate (funcCallMoreArgs funName) >>
            return (nullSubst, env, FunDecl funName args (Just funType) vars stmts)
        EQ -> do
            env' <- TImisc.insertID env funName funType GlobalScopeFun -- With only this function inserted
            env'' <- insertMore env' (zip3 args argTypes (replicate (length args) ArgScope)) -- With this function + args inserted
            (s1, env''', vars') <- tiVarDecls env'' vars LocalScope -- With this function + args + local varDecls inserted

            (s2,t1, stmts') <- tiStmts env''' stmts

            let cs1 = s2 `composeSubst` s1

            let t1' = fromMaybe (Void defaultLoc defaultLoc) t1
            s3 <- mgu (apply cs1 t1') retType

            let cs2 = s3 `composeSubst` cs1

            let funType' = apply cs2 funType
            let funDecl = FunDecl funName args (Just funType') (apply cs2 vars') (apply cs2 stmts')

            
            -- if (getID funName == "execute")
            --     then traceM ( red ++ "Execute\n" ++ printEnv (apply cs2 env''') ++ reset)
            --     else return ()

            -- let funcScheme = generalize env funType in
            --     return (cs2, TImisc.insert (apply cs2 env) funName funcScheme GlobalScopeFun, funDecl)

            (funDecl', s, overloaded) <- monomorphize funDecl env'''
            let (polyOp2, polyFunCall) = toListOL overloaded
            if  nullOL overloaded
                then
                    -- trace ("No 'poly' overloading in " ++ pp funName) $
                    -- let funcScheme = trace ("\n\nFree stuff in: " ++pp funName ++ "\n" ++ pp funType ++"\n" ++ pp (Set.toList $ ftv funType) ++ "\n\n" ++ pp (Set.toList $ ftv env)++ "\n\n") generalize env funType in
                    let funcScheme = generalize env funType in
                    return (cs2, TImisc.insert (apply cs2 env) funName funcScheme GlobalScopeFun, funDecl')
                else
                    -- trace ("Poly overloading in " ++ pp funName {-- ++ "\n\n" ++ show polyOp2 ++ "\n\n" ++ show polyFunCall --}) $ 
                    do
                        let (args', fType', scheme) = overloadFunction args (apply s funType) env polyOp2 polyFunCall
                        let FunDecl funName' _ (Just _) vars'' stmts'' = funDecl'
                        return (cs2, TImisc.insert (apply cs2 env) funName scheme GlobalScopeFun, FunDecl funName' args' (Just fType') vars'' stmts'')

tiFunDecl env (FunDecl funName args Nothing vars stmts) = do
    argTypes <- mapM (newSPLVarDLoc . getDLoc) args
    retType <- newSPLVar

    let fType = FunType (getFstLoc funName) argTypes retType (getSndLoc $ last args)
    env' <- TImisc.insertID env funName fType GlobalScopeFun -- With only this function inserted
    env'' <- insertMore env' (zip3 args argTypes (replicate (length args) ArgScope)) -- With this function + args inserted
    (s1, env''', vars') <- tiVarDecls env'' vars LocalScope -- With this function + args + local varDecls inserted

    (s2, t1, stmts') <- tiStmts env''' stmts

    let cs1 = s2 `composeSubst` s1
    let t1' = fromMaybe (Void defaultLoc defaultLoc) t1

    s3 <- mgu retType (apply cs1 t1') 
    let cs2 = s3 `composeSubst` cs1

    -- let Just (Scheme [] t) = find funName env'''


    -- trace ("HIERZO "++ pp funName ++ "\n" ++ printEnv env''' ++ printSubst (Map.toList cs1) ++  pp funType ++ "\nEND") $ do
    let funDecl = FunDecl funName args (Just $ apply cs2 fType) (apply cs2 vars') (apply cs2 stmts')
    -- let funDecl = FunDecl funName args (Just funType) vars' stmts'

    (funDecl', s, overloaded) <- monomorphize funDecl (apply cs2 env''')
    let (polyOp2, polyFunCall) = toListOL overloaded

    -- traceM (pp funName ++ " " ++ printSubst cs2 ++ red ++ show overloaded ++ reset)

    let funType = apply s $ apply cs2 fType


    if  nullOL overloaded
        then
            -- trace ("No 'poly' overloading in " ++ pp funName) $
            let funcScheme = generalize env funType in
            return (cs2, TImisc.insert (apply cs2 env) funName funcScheme GlobalScopeFun, funDecl')
        else do
                let (args', fType', scheme) = overloadFunction args funType env polyOp2 polyFunCall
                let FunDecl funName' _ (Just _) vars'' stmts'' = funDecl'
                return (cs2, TImisc.insert (apply cs2 env) funName scheme GlobalScopeFun, FunDecl funName' args' (Just fType') vars'' stmts'')

tiStmts :: TypeEnv -> [Stmt] -> TI (Subst, Maybe SPLType, [Stmt])
tiStmts env [] = return (nullSubst, Nothing, [])
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
    let Just a = retIf
    -- traceM ("IF RETURN " ++ pp a)
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
        return (cs1, Nothing, StmtAssignVar id (Field []) e' (Just $ apply cs1 t1))
    Nothing ->
        dictate (refBeforeDec "Variable:" id) >>
        return (nullSubst, Nothing, StmtAssignVar id (Field []) e typ)
tiStmt (TypeEnv env) (StmtAssignVar id (Field fields) e typ) = 
    let def = (nullSubst, Nothing, StmtAssignVar id (Field fields) e typ) in
    case Map.lookup id env of
        Just (scheme,s) | builtin id -> 
            dictate (assigningToStdFunction id) >>
            return def
        Nothing ->
            dictate (refBeforeDec "Variable:" id) >>
            return def
        Just (scheme,s) -> do
            tDef <- newSPLVarDLoc (getDLoc id)
            retDef <- newSPLVarLoc (getFstLoc id) (getSndLoc (last fields))
            let typeDef = (nullSubst, tDef, retDef)

            typeOfLeft <- instantiate scheme
            -- let locationT = injectLocType (getDLoc id) t
            
            -- traceM (red ++ pp id ++ " " ++ pp t ++ reset)

            (s1, typeOfe, e') <- tiExp (TypeEnv env) e
            (s2, typeOfLeft', ret) <- injectErrLoc typeDef (getType typeOfLeft fields) (getDLoc id)
            let cs1 = s2 `composeSubst` s1
            s3 <- mgu (apply cs1 ret) (apply cs1 typeOfe)
            let cs2 = s3 `composeSubst` cs1
            
            -- traceM (red ++ 
            --             pp id ++ " " ++ pp typeOfLeft ++ " " ++ 
            --             pp typeOfLeft' ++  " " ++ 
            --             pp ret ++ " " ++ 
            --             pp typeOfe ++ " " ++ 
            --             reset)

            -- traceM (red ++ 
            --             pp id ++ " " ++ pp (apply cs2 typeOfLeft) ++ " " ++ 
            --             pp (apply cs2 typeOfLeft') ++  " " ++ 
            --             pp (apply cs2 ret) ++ " " ++ 
            --             pp (apply cs2 typeOfe) ++ " " ++ 
            --             reset)
            -- traceM ("\n" ++ printSubst cs1 ++"\n")
            -- s4 <- mgu (apply cs2 typeOfLeft') typeOfLeft
            -- let cs3 = s4 `composeSubst` cs2
            return (cs2, Nothing, StmtAssignVar id (Field fields) e' (Just $ apply cs2 ret))

typeCheckExps :: IDLoc -> Bool -> TypeEnv -> Subst -> [Exp] -> [Op2Typed] -> [FunCall] -> [SPLType] -> TI (Subst, [Exp],Overloaded)
typeCheckExps id _ env s [] _ _ [] = do
    return (s, [], emptyOL)
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

    (s1, t1, e') <- injectErrLoc def (tiExp env e) (getDLoc e)
    let cs1 = s1 `composeSubst` s

    -- traceM (pp id ++ " " ++pp (apply cs1 t) ++ " " ++ pp t1 ++ " " ++ show (getDLoc e))

    s2 <- injectErrLoc nullSubst (mgu t1 (apply cs1 t)) (getDLoc e)

    let cs2 = s2 `composeSubst` cs1
    (s3, es', ol) <- typeCheckExps id monomorph (apply cs1 env) cs2 es ops funcs ts
    return (s3 `composeSubst` cs2 , e':es', ol)
typeCheckExps id monomorph env s [] (op:ops) funcs (t:ts) = do
    let (Op2 op' (Just opType) loc) = apply s op
    s1 <- mgu t opType
    let cs1 = s1 `composeSubst` s
    let opType1 = apply cs1 opType
    let FunType locF1 argTypes _ locF2 = opType1

    if containsIDType opType1
        then
            if monomorph
                then do
                    let name = idLocCreator $ overloadedOpName op' (head argTypes)
                
                    let exp = ExpId name (Field [])
                    (s2,es',ol1) <- typeCheckExps id monomorph env cs1 [] ops funcs ts
                    let ol2 = singletonOLOp (Op2 op' (Just opType1) loc)
                    let ol3 = ol2 `unionOL` ol1
                    return (s2 `composeSubst` cs1, exp:es', ol3)
                else do
                    let name = idLocCreator $ overloadedOpName op' (head argTypes)
                    (s2,es',ol1) <- typeCheckExps id monomorph env cs1 [] ops funcs ts
                    let ol2 = singletonOLOp (Op2 op' (Just opType1) loc)

                    return (s2 `composeSubst` cs1, es', ol2 `unionOL` ol1)
        else do
                -- Everything about the opType1 is known, we can thus insert safely.
                a <- insertOp2TI (Op2 op' (Just opType1) loc)

                let name = overloadedOpName op' (head argTypes)
                let exp = ExpFunction defaultLoc (idLocCreator name) defaultLoc (Just opType1)
                (s2,es', ol) <- typeCheckExps id monomorph env cs1 [] ops funcs ts
                return (s2 `composeSubst` cs1, exp:es', ol)
typeCheckExps id monomorph env s [] [] (func:funcs) (t:ts) = do
    let (FunCall locF (ID locA id' locB) es locF' (Just funcType)) = apply s func
    s1 <- mgu t funcType
    let cs1 = s1 `composeSubst` s
    let funcType' = apply cs1 t
    let FunType locF1 argTypes _ locF2 = funcType'

    -- trace ("typeCheckExps func: "++ id' ++ " mono: "++ show monomorph ++ " " ++pp id ++ " \n"++ pp funcType ++ "\n" ++ pp funcType' ++ "\n" ++ pp t ++ "\n" ++ pp (apply cs1 t) ) $
    if containsIDType funcType'
    then
        if monomorph
            then do
                let name = ID locA (overloadedTypeName "print" (head argTypes)) locB
                let exp = ExpId name (Field [])
                (s2,es',ol) <- typeCheckExps id monomorph env cs1 [] [] funcs ts
                let overloaded = singletonOLFun (FunCall locF name es locF' (Just funcType'))
                return (s2 `composeSubst` cs1, exp:es', overloaded `unionOL` ol)
            else do
                let name = ID locA (overloadedTypeName "print" (head argTypes)) locB
                -- let exp = ExpFunction defaultLoc name defaultLoc (Just funcType')
                (s2,es',ol) <- typeCheckExps id monomorph env cs1 [] [] funcs ts
                let overloaded = singletonOLFun (FunCall locF name es locF' (Just  funcType'))
                return (s2 `composeSubst` cs1, es', overloaded `unionOL` ol)
    else do
        -- Everything about the FunCall is known, we can thus insert safely.
        a <- insertFunCallTI (FunCall locF (ID locA "print" locB) es locF' (Just funcType'))
        let name = overloadedTypeName "print" (head argTypes)
        let exp = ExpFunction defaultLoc (idLocCreator name) defaultLoc (Just funcType')
        (s2,es',ol) <- typeCheckExps id monomorph env cs1 [] [] funcs ts
        return (s2 `composeSubst` cs1, exp:es',ol)
typeCheckExps id mono env s exps _ _ argTypes = confess (Error defaultLoc (pp exps ++ "\n" ++ pp argTypes)  )

tiExpsList :: TypeEnv -> [Exp] -> TI (Subst, SPLType, Exp)
tiExpsList env [e] = do
    (s1, t1, e') <- tiExp env e
    let DLoc locA locB = getDLoc e
    let arrayType = let (DLoc locA locB) = getDLoc t1 in ArrayType locA t1 locB
    let opType = Op2 Con (Just $ FunType locA [t1,arrayType] arrayType locB)
    return (s1, t1, ExpOp2 locA e' (opType locA) (ExpEmptyList locA locB) locB)
tiExpsList env (e:es) = do
    (s1, t1, e' ) <- tiExp env e
    (s2, t2, es') <- tiExpsList (apply s1 env) es
    let cs1 = s2 `composeSubst` s1
    s3 <- injectErrLoc nullSubst (mgu (apply cs1 t1) t2) (getDLoc e)
    let DLoc locA locB = getDLoc e
    let cs2 = s3 `composeSubst` cs1

    let arrayType = ArrayType locA t2 locB
    let opType = Op2 Con (Just $ FunType locA [t1,arrayType] arrayType locB)

    return (cs2, t2, ExpOp2 (getFstLoc e) e' (opType (getFstLoc e)) es' (getSndLoc e))

tiExp :: TypeEnv -> Exp -> TI (Subst, SPLType, Exp)
tiExp (TypeEnv env) (ExpId id (Field [])) = do
    case Map.lookup id env of
        Just (OverScheme lVars lT lOps lFuncs, _) -> 
            confess (overloadedAsArgument id)
        Just (scheme,s) -> do
            t <- instantiate scheme
            if isFunctionType t && s == GlobalScopeFun
                then tiExp (TypeEnv env) (ExpFunction (getFstLoc id) id (getSndLoc id) Nothing)
                else return (nullSubst, t, ExpId id (Field []))
        Nothing -> do
            t <- newSPLVar
            dictate (refBeforeDec "Variable:" id) >> return (nullSubst, t, ExpId id (Field []))
tiExp (TypeEnv env) (ExpId id (Field fields)) = case Map.lookup id env of
    Just (OverScheme lVars lT lOps lFuncs, _) -> 
        confess (overloadedAsArgument id)
    Just (Scheme lVars lT,s) -> do
        t <- instantiate (Scheme lVars lT)
        if isFunctionType t
            then do
                newT <- newSPLVar
                let err = appliedStdOnFunction fields id (DLoc (getFstLoc (head fields)) (getSndLoc (last fields)))
                dictate err >> return (nullSubst, newT, ExpId id (Field fields) )
            else do
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

    (t1, t2, t3, opType) <- op2Type op (getDLoc e1) (getDLoc e2) (DLoc locA locB)
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
tiExp env (ExpFunCall funCall) = do
    (s1, t, funCall', _) <- tiFunCall env False funCall
    return (s1, t, ExpFunCall funCall')

tiExp (TypeEnv env) (ExpFunction locA function locB Nothing) = do
    case Map.lookup function env of
        Just (Scheme lockedVars lockedT,_) -> do
            t' <- instantiate (Scheme lockedVars lockedT)
            return (nullSubst, t', ExpFunction locA function locB (Just t'))
        _ -> confess (Error defaultLoc  "shit on  on 558")
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

tiFunCall :: TypeEnv -> Bool -> FunCall -> TI (Subst, SPLType, FunCall, Overloaded)
tiFunCall (TypeEnv env) monomorph (FunCall locA id args locB _) = do
    case Map.lookup id env of
        Just (OverScheme lockedvars lockedType lockedOps lockedFuncs,s) | isGlobalScope s -> do

            -- traceM (yellow ++ pp id ++ " " ++ show monomorph ++ reset)
            (t, ops, funcs) <- instantiateOver (OverScheme lockedvars lockedType lockedOps lockedFuncs)
            (s1, args',ol) <- typeCheckExps id monomorph (TypeEnv env) nullSubst args ops funcs (getArgTypes t)
            let returnType = getReturnType t
            
            return (s1, apply s1 returnType, FunCall locA id args' locB (Just $ apply s1 t),ol)
        Just (OverScheme lVars lT lOps lFuncs, _) -> 
            confess (overloadedAsArgument id)
        Just (scheme,s) | isGlobalScope s -> do
            t <- instantiate scheme
            (s1, args', ol) <- typeCheckExps id monomorph (TypeEnv env) nullSubst args [] [] (getArgTypes t)

            let returnType = getReturnType t
            return (s1, apply s1 returnType, FunCall locA id args' locB (Just $ apply s1 t), ol)
        Just (scheme, ArgScope) -> do
            t <- instantiate scheme
            funType <- if isFunctionType t
                then return t
                else do
                    argTypes <- mapM (newSPLVarDLoc . getDLoc) args
                    FunType locA argTypes <$> newSPLVarLoc locA locB <*> pure locB

            s1 <- injectErrLoc nullSubst (mgu funType t) (DLoc locA locB)
            
            (s2, args', ol) <- typeCheckExps id monomorph (TypeEnv env) nullSubst args [] [] (getArgTypes funType)
            let returnType = getReturnType funType
            let cs1 = s2 `composeSubst` s1
            return (cs1, apply cs1 returnType, FunCall locA id args' locB (Just $ apply cs1 funType), ol)
        Just (scheme, LocalScope) -> do
            t <- instantiate scheme
            funType <- if isFunctionType t
                then return t
                else do
                    argTypes <- mapM (newSPLVarDLoc . getDLoc) args
                    FunType locA argTypes <$> newSPLVarLoc locA locB <*> pure locB

            s1 <- injectErrLoc nullSubst (mgu funType t) (DLoc locA locB)
            
            (s2, args', ol) <- typeCheckExps id monomorph (TypeEnv env) nullSubst args [] [] (getArgTypes funType)
            let returnType = getReturnType funType
            let cs1 = s2 `composeSubst` s1
            return (cs1, apply cs1 returnType, FunCall locA id args' locB (Just $ apply cs1 funType), ol)
        Nothing -> do
            t <- newSPLVar
            dictate (refBeforeDec "Function:" id) >> return (nullSubst, t, FunCall locA id args locB Nothing, emptyOL)
        -- x -> confess (Error defaultLoc  ("Did not expect"++show x))

-- ===================== Monomorphization ============================
class Monomorphization a where
    monomorphize :: a -> TypeEnv -> TI (a, Subst, Overloaded)

instance Monomorphization a => Monomorphization [a] where
    monomorphize [] env = return ([],nullSubst, emptyOL)
    monomorphize (x:xs) env = do
        (a,s1, b) <- monomorphize x env
        (as,s2, b') <- monomorphize xs env
        let cs1 = s2 `composeSubst` s1
        return (a:as, cs1, b`unionOL`b')

instance Monomorphization FunDecl where
    monomorphize (FunDecl funName args fType vars stmts) env = do
        (vars', s1, ol1) <- monomorphize vars  env
        (stmts', s2, ol2) <- monomorphize stmts env
        let cs1 = s2 `composeSubst` s1
        return (FunDecl funName args fType vars' stmts', cs1, ol1 `unionOL` ol2)

instance Monomorphization Stmt where
    monomorphize (StmtIf e stmts (Just els) loc) env = do
        (e',s1, ol1) <- monomorphize e env
        (stmts',s2, ol2) <- monomorphize stmts env
        (els',s3, ol3) <- monomorphize els env
        let cs1 = s3 `composeSubst` s2 `composeSubst` s1
        return (StmtIf e' stmts' (Just els') loc, cs1, ol1 `unionOL` ol2 `unionOL` ol3)
    monomorphize (StmtIf e stmts Nothing loc) env = do
        (e', s1, ol1) <- monomorphize e env
        (stmts', s2, ol2) <- monomorphize stmts env
        let cs1 =  s2 `composeSubst` s1
        return (StmtIf e stmts Nothing loc,cs1, ol1 `unionOL` ol2)
    monomorphize (StmtWhile e stmts loc) env = do
        (e', s1, ol1) <- monomorphize e env
        (stmts', s2, ol2) <- monomorphize stmts env
        let cs1 =  s2 `composeSubst` s1
        return (StmtWhile e' stmts' loc, cs1, ol1 `unionOL` ol2)
    monomorphize (StmtAssignVar id fields e t) env = do
        (e',s, ol1) <- monomorphize e env
        return (StmtAssignVar id fields e' t,s, ol1)
    monomorphize (StmtFuncCall funCall loc) env = do
        (funCall',s1, ol1) <- monomorphize funCall env
        return (StmtFuncCall funCall' loc,s1, ol1)
    monomorphize (StmtReturn (Just e) loc) env = do
        (e',s, ol1) <- monomorphize e env
        return (StmtReturn (Just e') loc,s, ol1)
    monomorphize x env = return (x,nullSubst, emptyOL)

instance Monomorphization VarDecl where
    monomorphize (VarDeclType t id e) env = do
        (e',s, ol1) <- monomorphize e env
        return (VarDeclType t id e',s, ol1)
    monomorphize x env = return (x,nullSubst, emptyOL)

instance Monomorphization Exp where
    monomorphize (ExpBracket e) env = do
        (e',s, ol1) <- monomorphize e env
        return (ExpBracket e',s, ol1)
    monomorphize (ExpOp1 locA op e locB) env = do
        (e',s, ol1) <- monomorphize e env
        return (ExpOp1 locA op e' locB,s, ol1)
    monomorphize (ExpList locA exps locB t) env = do
        (exps',s, ol1) <- monomorphize exps env
        return (ExpList locA exps' locB t,s, ol1)
    monomorphize (ExpTuple locA (e1, e2) locB t) env = do
        (e1',s1, ol1) <- monomorphize e1 env
        (e2',s2,  ol2) <- monomorphize e2 env
        let cs1 =  s2 `composeSubst` s1
        return (ExpTuple locA (e1', e2') locB t,cs1, ol1 `unionOL` ol2)
    monomorphize (ExpOp2 locA e1 (Op2 op (Just (FunType locF1 t t' locF2)) loc) e2 locB) env | containsIDType (FunType locF1 t t' locF2) && op /= Con = do
        let name = idLocCreator $ overloadedOpName op (head t)
        (e1',s1, ol1) <- monomorphize e1 env
        (e2',s2, ol2) <- monomorphize e2 env
        let cs1 =  s2 `composeSubst` s1
        let exp = ExpFunCall (FunCall locA name [e1',e2'] locB (Just (FunType locF1 t t' locF2)))
        return (exp,cs1, singletonOLOp (Op2 op (Just (FunType locF1 t t' locF2)) loc) `unionOL` (ol1 `unionOL` ol2))
    monomorphize (ExpOp2 locA e1 (Op2 op (Just (FunType locF1 t t' locF2)) loc) e2 locB) env = do
        -- let name = idLocCreator $ overloadedOpName op (head t)
        (e1',s1, ol1) <- monomorphize e1 env
        (e2',s2, ol2) <- monomorphize e2 env
        let cs1 =  s2 `composeSubst` s1
        let exp = ExpOp2 locA e1' (Op2 op (Just (FunType locF1 t t' locF2)) loc) e2' locB
        return (exp,cs1, ol1 `unionOL` ol2)
    monomorphize (ExpFunCall funCall) env = do
        (funCall', s, ol1) <- monomorphize funCall env
        return (ExpFunCall funCall', s, ol1)
    monomorphize (ExpId id (Field [])) (TypeEnv env) =
        case Map.lookup id env of
            Just (OverScheme lockerVars lockedT lockedOps lockedFuncs,s) -> do
                (t, ops, funcs) <- instantiateOver $ OverScheme lockerVars lockedT lockedOps lockedFuncs
                return (ExpId id (Field []),nullSubst, toOLOpFun ops funcs )
            _ -> return (ExpId id (Field []),nullSubst, emptyOL)
    monomorphize x env = return (x, nullSubst, emptyOL)

instance Monomorphization FunCall where
    monomorphize (FunCall locA (ID idLocA "print" idLocB) args locB (Just (FunType locF1 t t' locF2))) env | containsIDType (FunType locF1 t t' locF2) = do
        let name = idLocCreator $ overloadedTypeName "print" (head t)
        (args',s1, ol1) <- monomorphize args env
        return
            (FunCall locA name args' locB (Just (FunType locF1 t t' locF2)),
            s1,
            singletonOLFun (FunCall locA name args' locB (Just (FunType locF1 t t' locF2))) `unionOL` ol1)
    monomorphize (FunCall locA id args locB t) env | containsIDTypeMaybe t = do
        defT <- newSPLVar
        let def = (nullSubst, defT, FunCall locA id args locB t,emptyOL)
        
        -- traceM (green ++ pp id ++ " " ++ show True ++ reset)
        (s,_,funcall,overloaded) <- tiFunCall env True (FunCall locA id args locB t)
        -- traceM (green ++ printSubst s ++ reset)

        -- trace ( "\nMonomorphizing "++pp id++"\n"++show overloaded ++ "\nEND\n") $ 
        return (funcall, s, overloaded)
    monomorphize (FunCall locA id args locB t) env = do
        -- traceM (red ++ pp id ++ " " ++ show True ++ reset)
        return (FunCall locA id args locB t, nullSubst, emptyOL)



instance Monomorphization Op2Typed where
    monomorphize (Op2 op (Just (FunType locF1 t t' locF2)) loc) env | containsIDType (FunType locF1 t t' locF2) && op /= Con = do
        let name = idLocCreator $ overloadedOpName op (head t)
        return (Op2 op (Just (FunType locF1 t t' locF2)) loc,
                nullSubst,
                singletonOLOp (Op2 op (Just (FunType locF1 t t' locF2)) loc))
    monomorphize x env = return (x, nullSubst, emptyOL)

-- ===================== Main Type Inference ============================
typeInference :: SPL -> Either Error (Subst, TypeEnv, SPL, (Map String Op2Typed, Map String FunCall))
typeInference code = do
    case runTI (tiSPL code) of
        (That (s1, env, spl), (_,maps)) -> do
            -- let SPL code' = apply s1 spl
            let SPL code' = spl
            -- cleanCode <- removeDeadCode (SPL $ removeMutRec code')
            let cleanCode = SPL $ removeMutRec code'
            let updatedCode = apply s1 cleanCode
            Right (s1, env, updatedCode, maps)
        (These errs a, state) -> Left errs
        (This errs, state) -> Left errs

tokenizeParserTI file = tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference


mainTIIO filename = do

    file <- readFile  ("../SPL_test_code/" ++ filename)
    case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
        Right (s1, env, code, maps) -> do
            putStr $ pp code
            putStr $ printOverloading maps
            putStr $ printEnv env
            putStr $ printSubst s1
        Left x -> putStr $ showError file x


mainTI filename = do
    -- path <- getCurrentDirectory
    -- print path
    file <- readFile  ("../SPL_test_code/" ++ filename)
    case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= rtga >>= typeInference of
        Right (s1, env, code, maps) -> do
            writeFile "../SPL_test_code/ti-out.spl"$ pp code
            putStr $ printOverloading maps
            putStr $ printEnv env
            -- putStr $ printSubst s1
        Left x -> putStr $ showError file x

