module TI where

import Error
import Lexer
import AST
import Parser
import MutRec

import Data.Map as Map
import Data.Set as Set
import Data.Maybe
import Data.These
import Data.Bifunctor as BI ( Bifunctor(first) ) 

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Chronicle
import Control.Monad.State

import System.Exit
import System.Directory
import Debug.Trace

-- ===================== Type inference data types ============================
type TIState = (Int, (Map String Op2Typed, Map String FunCall))
type TI a = ChronicleT Error (State TIState) a

runTI :: TI a -> (These Error a, TIState)
runTI t = runState (runChronicleT t) initTIState
  where initTIState = (0, (Map.empty, Map.empty))

-- ===================== TypeEnv ============================
newtype TypeEnv = TypeEnv (Map IDLoc (Scheme,Scope))
    deriving (Show)

insert :: TypeEnv -> IDLoc -> Scheme -> Scope -> TypeEnv
insert (TypeEnv env) id scheme s = TypeEnv (Map.insert id (scheme,s) env)

insertID :: TypeEnv -> IDLoc -> SPLType -> Scope -> TI TypeEnv
insertID (TypeEnv env) id t s = 
    case lookupKey id env of
        Just((scheme,s'),id') | s==s'-> dictate (doubleDef2 id id') >> return (TypeEnv env)
        Nothing -> return $ TypeEnv (Map.insert id (Scheme [] t,s) env)

insertMore :: TypeEnv -> [(IDLoc,SPLType,Scope)] -> TI TypeEnv
insertMore env [] = return env
insertMore (TypeEnv env) ((id,t,s):xs) = 
    case lookupKey id env of
        Just((scheme,s'),id') | s==s'-> dictate (doubleDef2 id id') >> insertMore (TypeEnv env) xs
        _ -> insertMore (TypeEnv (Map.insert id (Scheme [] t,s) env)) xs

remove :: TypeEnv -> IDLoc -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

find :: IDLoc -> TypeEnv -> Maybe Scheme
find id (TypeEnv env) = fst <$> Map.lookup id env

generalize :: TypeEnv -> SPLType -> Scheme
generalize env t  = Scheme vars t
  where vars = Set.toList (ftv t Set.\\ ftv env)

generalizeFuncs :: TypeEnv -> [IDLoc] -> TI TypeEnv
generalizeFuncs env [] = return env
generalizeFuncs (TypeEnv env) (x:xs) = case Map.lookup x env of
    Just (Scheme _ t,scope) -> let scheme = generalize (TypeEnv env) t in
        generalizeFuncs (TypeEnv $ Map.insert x (scheme,GlobalScope) env) xs
    _ -> 
        dictate (ErrorD (getDLoc x) ("Function " ++ pp x ++  " is mutual recursive and should therefore be in the type environment but it is not.")) >>
        return (TypeEnv env)

-- ===================== Scheme ============================
data Scheme = 
    Scheme [IDLoc] SPLType |
    OverScheme [IDLoc] SPLType [Op2Typed] [FunCall]
    deriving (Show, Eq)

data Scope = GlobalScope | LocalScope | ArgScope
    deriving (Show,Eq)

instantiate :: Scheme -> TI SPLType
instantiate (Scheme vars t) = do 
    nvars <- mapM (const newSPLVar) vars
    let s = Map.fromList (zip vars nvars)
    return $ apply s t
instantiate (OverScheme vars t _ _) = do
    nvars <- mapM (const newSPLVar) vars
    let s = Map.fromList (zip vars nvars)
    return $ apply s t


-- ===================== Substitution ============================
type Subst = Map.Map IDLoc SPLType

nullSubst :: Subst
nullSubst = Map.empty

applySubst :: Subst -> Subst -> Subst
applySubst s1 = Map.map $ apply s1

composeSubst::Subst -> Subst -> Subst
composeSubst s1 s2 = Map.map (apply s1) s2 `Map.union` s1

-- ===================== ftv and apply implementations ============================
class Types a where
    ftv :: a -> Set IDLoc
    apply :: Subst -> a -> a

instance Types a => Types [a] where
    ftv l = Prelude.foldr (Set.union . ftv) Set.empty l
    apply s = Prelude.map (apply s)

instance Types TypeEnv where
    ftv (TypeEnv env)      =  ftv (Prelude.map fst (Map.elems env))
    apply s (TypeEnv env)  =  TypeEnv (Map.map (BI.first (apply s)) env)

instance Types Scheme where
    ftv (Scheme vars t) = ftv t Set.\\ Set.fromList vars
    apply s (Scheme vars t) = Scheme vars (apply (Prelude.foldr Map.delete s vars) t)

instance Types SPLType where
    ftv (Void _ _) = Set.empty
    ftv (TypeBasic _ x _) = Set.empty
    ftv (TupleType _ (x,y) _) = ftv x `Set.union` ftv y
    ftv (ArrayType _ x _) = ftv x
    ftv (FunType args ret) = ftv args `Set.union` ftv ret
    ftv (IdType x ) = Set.singleton x
    apply s (IdType x) = case Map.lookup x s of
                        Just t -> t
                        Nothing -> IdType x
    apply s (FunType args ret) = FunType (apply s args) (apply s ret)
    apply s (TupleType locA (x,y) locB) = TupleType locA (apply s x, apply s y) locB
    apply s (ArrayType locA x locB) = ArrayType locA (apply s x) locB
    apply _ x = x

instance Types a =>  Types (Maybe a) where
    ftv (Just a) = ftv a
    ftv Nothing = Set.empty
    apply s (Just a) = Just $ apply s a
    apply s Nothing = Nothing

newSPLVar :: TI SPLType
newSPLVar =
    do  (s,overloaded) <- get
        put (s+1,overloaded)
        return $ IdType (idLocCreator (reverse (toTyVar s)))
  where
    toTyVar :: Int -> String
    toTyVar c | c < 26    =  [toEnum (97+c)]
              | otherwise = let (n, r) = c `divMod` 26
                            in toEnum (97+r) : toTyVar (n-1)

newSPLVarLoc :: Loc -> TI SPLType
newSPLVarLoc loc =
    do  (s,overloaded) <- get
        put (s+1,overloaded)
        return $ IdType (ID loc (reverse (toTyVar s)) loc )
  where
    toTyVar :: Int -> String
    toTyVar c | c < 26    =  [toEnum (97+c)]
              | otherwise = let (n, r) = c `divMod` 26
                            in toEnum (97+r) : toTyVar (n-1)

-- ===================== Most General Unifier ============================
class MGU a where
    mgu :: a -> a -> TI Subst
    generateError :: a -> a -> Error

instance MGU a => MGU [a] where
    mgu [] [] = return nullSubst
    mgu (x:xs) (y:ys) = do s1 <- mgu x y
                           s2 <- mgu xs ys
                           return (s1 `composeSubst` s2)
    generateError xs ys = undefined

instance MGU a => MGU (Maybe a) where
    mgu (Just l) (Just r) = mgu l r
    mgu Nothing _ = return nullSubst
    mgu _ Nothing = return nullSubst
    generateError (Just l) (Just r) = generateError l r
    generateError Nothing _ = undefined 
    generateError _ Nothing = undefined 

instance MGU SPLType where
    mgu (FunType arg ret) (FunType arg' ret') = do
        s1 <- mgu arg arg'
        s2 <- mgu (apply s1 ret) (apply s1 ret')
        return (s2 `composeSubst` s1)

    mgu (FunType arg ret) t1 = confess $ generateError (FunType arg ret) t1
    mgu t1 (FunType arg ret) = confess $ generateError (FunType arg ret) t1

    mgu (TypeBasic _ x _) (TypeBasic _ y _) | x == y = return nullSubst
    -- mgu (TypeBasic locA x locB) (TypeBasic locA' y locB') = 
    --     dictate (generateError (TypeBasic locA x locB) (TypeBasic locA' x locB')) >>
    --     return nullSubst

    mgu (Void _ _) (Void _ _) = return nullSubst

    mgu (TupleType  _ (l1,r1) _) (TupleType _ (l2,r2) _) = do
        s1 <- mgu l1 l2
        s2 <- mgu r1 r2
        return (s1 `composeSubst` s2)
    mgu (ArrayType _ x _) (ArrayType _ y _) = mgu x y

    mgu (IdType id) r | not $ isFun r = varBind id r
    mgu l (IdType id) | not $ isFun l = varBind id l

    mgu t1 t2 =
        dictate (generateError t1 t2) >>
        return nullSubst

    generateError t1 t2 = case getFstLoc t1 `compare` getFstLoc t2 of
        LT -> ErrorD (getDLoc t2) ("Type "++ pp t1 ++" does not unify with: " ++ pp t2 ++" "++ showLoc t2)
        GT -> ErrorD (getDLoc t1) ("Type "++ pp t1 ++" "++ showLoc t1 ++" does not unify with: " ++ pp t2 ++" "++ showLoc t2)
        EQ -> case getDLoc t2 of
                        (DLoc (Loc (-1) (-1)) _) -> Error defaultLoc ("Types do not unify: " ++ pp t1 ++ " vs. " ++ pp t2)
                        x -> ErrorD x ("Type "++ pp t1 ++" "++ showLoc t1 ++" does not unify with: " ++ pp t2 ++" "++ showLoc t2)

varBind :: IDLoc -> SPLType -> TI Subst
varBind id (IdType t) | id == t = return nullSubst
varBind id (IdType t) = return $ Map.singleton id (IdType t)
varBind id t | id `Set.member` ftv t = 
    dictate (Error defaultLoc ("occurs check fails: " ++ pp id ++ " vs. " ++ show t)) >>
    return nullSubst
varBind id t = return $ Map.singleton id t

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
        Just((scheme,s'),id') | s==s'-> dictate (doubleDef2 id id') >>
            return (nullSubst, TypeEnv env, VarDeclVar id e)
        _ -> do
            (s1, t1, e') <- tiExp (TypeEnv env) e
            let scheme = Scheme [] t1
            let env' = TypeEnv (Map.insert id (scheme,s) env)
            return (s1, apply s1 env', VarDeclType t1 id e')
tiVarDecl (TypeEnv env) (VarDeclType t id e) s = 
    case lookupKey id env of
        Just((scheme,s'),id') | s==s'-> dictate (doubleDef2 id id') >>
            return (nullSubst, TypeEnv env, VarDeclType t id e)
        _ -> do
            (s1, t1, e') <- tiExp (TypeEnv env) e
            s2 <- mgu (apply s1 t) t1
            let cs1 = s2 `composeSubst` s1
            let scheme = Scheme [] t1
            let env' = TypeEnv (Map.insert id (scheme,s) env)
            return (cs1, apply cs1 env', VarDeclType (apply cs1 t) id e')

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
tiFunDecl env (FunDecl funName args (Just funType) vars stmts) =
    if not $ isGoodScope GlobalScope funName env 
        then dictate (applVarAsFunc funName) >> return (nullSubst, env, FunDecl funName args (Just funType) vars stmts) 
        else do
            let (argTypes, retType) = let a = getArgsTypes funType in (init a, last a)

            case length args `compare` length argTypes of
                LT -> 
                    dictate (funcCallLessArgs funName) >>
                    return (nullSubst, env, FunDecl funName args (Just funType) vars stmts)
                GT -> 
                    dictate (funcCallMoreArgs funName) >>
                    return (nullSubst, env, FunDecl funName args (Just funType) vars stmts)
                EQ -> do
                    env' <- TI.insertID env funName funType GlobalScope -- With only this function inserted
                    env'' <- insertMore env' (zip3 args argTypes (replicate (length args) ArgScope)) -- With this function + args inserted
                    (s1, env''', vars') <- tiVarDecls env'' vars LocalScope -- With this function + args + local varDecls inserted

                    (s2,t1, stmts') <- tiStmts env''' stmts

                    let cs1 = s2 `composeSubst` s1

                    let t1' = fromMaybe (Void defaultLoc defaultLoc) t1
                    s3 <- mgu (apply cs1 t1') retType

                    let cs2 = s3 `composeSubst` cs1

                    let Just (Scheme _ funType') = find funName (apply cs2 env''')
                    let func = generalize env funType'

                    return (cs2, TI.insert env' funName func GlobalScope, FunDecl funName args (Just funType') vars' stmts')
tiFunDecl env (FunDecl funName args Nothing vars stmts) =
    if not $ isGoodScope GlobalScope funName env 
        then dictate (applVarAsFunc funName) >> return (nullSubst, env, FunDecl funName args Nothing vars stmts) 
        else do

            argTypes <- replicateM (length args) newSPLVar
            retType <- newSPLVar

            let fType = if not (Prelude.null argTypes) then foldr1 FunType (argTypes ++ [retType]) else retType
            env' <- TI.insertID env funName fType GlobalScope -- With only this function inserted
            env'' <- insertMore env' (zip3 args argTypes (replicate (length args) ArgScope)) -- With this function + args inserted
            (s1, env''', vars') <- tiVarDecls env'' vars LocalScope -- With this function + args + local varDecls inserted

            (s2, t1, stmts') <- tiStmts env''' stmts

            let cs1 = s2 `composeSubst` s1
            let t1' = fromMaybe (Void defaultLoc defaultLoc) t1

            s3 <- mgu (apply cs1 t1') retType
            let cs2 = s3 `composeSubst` cs1

            -- let Just (Scheme _ funType') = find funName (apply cs2 env''')
            let funType = apply cs2 fType

            let funDecl = FunDecl funName args (Just funType) (apply cs2 vars') (apply cs2 stmts')

            (funDecl', polyOp2, polyFunCall) <- monomorphize funDecl
            -- let (polyExp, polyFunCall) = findOverloadedFuncs vars' stmts'

            if  Prelude.null polyOp2 && Prelude.null polyFunCall
            -- if  True
                then
                    trace ("No 'poly' overloading in " ++ pp funName) $ 
                    let funcType = generalize env funType in
                    return (cs2, TI.insert (apply cs2 env) funName funcType GlobalScope, FunDecl funName args (Just funType) vars' stmts')
                else 
                    -- dictate (Error defaultLoc ("WE GOT ONE BOYS" ++ pp funName ++ "\n\n" ++ show polyExp ++ "\n\n" ++ show polyFunCall)) >>
                    trace ("WE GOT ONE BOYS " ++ pp funName ++ "\n\n" ++ show polyOp2 ++ "\n\n" ++ show polyFunCall) $
                    let (args', fType', scheme) = overloadFunction args funType env polyOp2 polyFunCall in
                    return (nullSubst, TI.insert (apply cs2 env) funName scheme GlobalScope, FunDecl funName args' (Just fType') vars stmts)


tiStmts :: TypeEnv -> [Stmt] -> TI (Subst, Maybe SPLType, [Stmt])
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
    (s1, t, funCall') <- tiFunCall env funCall
    return (s1, Nothing, StmtFuncCall  funCall' loc)

tiStmt env (StmtReturn Nothing (Loc line col)) = 
    return (nullSubst, Just (Void (Loc line col) (Loc line (col+6))), StmtReturn Nothing (Loc line col))
tiStmt env (StmtReturn (Just e) loc) = do
    (s1, t1, e') <- tiExp env e
    return (s1, Just t1, StmtReturn (Just e') loc)

tiStmt (TypeEnv env) (StmtAssignVar id (Field []) e typ) = case Map.lookup id env of
    Just (Scheme ids t,s)  -> do
        (s1, t1, e') <- tiExp (TypeEnv env) e
        s2 <- mgu (apply s1 t) t1
        let cs1 = s2 `composeSubst` s1
        return (cs1, Nothing, StmtAssignVar id (Field []) e' (Just t1))
    Nothing -> 
        dictate (refBeforeDec "Variable:" id) >> 
        return (nullSubst, Nothing, StmtAssignVar id (Field []) e typ)
tiStmt (TypeEnv env) (StmtAssignVar id (Field fields) e typ) = case Map.lookup id env of
    Just (Scheme ids t,s)  -> do
        (s1, t1, e') <- tiExp (TypeEnv env) e
        (s2, t', ret) <- getType t fields
        let cs1 = s2 `composeSubst` s1
        s3 <- mgu (apply cs1 ret) t1
        let cs2 = s3 `composeSubst` cs1
        s4 <- mgu (apply cs2 t') t
        let cs3 = s4 `composeSubst` cs2
        return (cs3, Nothing, StmtAssignVar id (Field fields) e' (Just $ apply cs3 ret))
    Nothing -> 
        dictate (refBeforeDec "Variable:" id) >>
        return (nullSubst, Nothing, StmtAssignVar id (Field fields) e typ)

typeCheckExps :: IDLoc -> TypeEnv -> [Exp] -> [SPLType] -> TI (Subst, [Exp])
typeCheckExps id env [] [] = return (nullSubst, [])
typeCheckExps id env [x] [] = dictate (funcCallMoreArgs id ) >> return (nullSubst, [])
typeCheckExps id env [] [x] = dictate (funcCallLessArgs id) >> return (nullSubst, [])
typeCheckExps id env (e:es) (t:ts) = do
    defType <- newSPLVar
    let def = (nullSubst, defType, e)

    (s1, t1, e') <- injectErrMsgAddition def (tiExp env e) (getDLoc e) "typeCheckExps"
    -- s2 <- trace ("Type " ++pp e ++ " " ++  pp t ++ " "++ pp t1) $ injectErrLocMsg nullSubst (mgu (apply s1 t) t1) (getDLoc e) ("Argument '"++ pp e ++ "' should have type "++ pp t)
    s2 <- injectErrLoc nullSubst (mgu (apply s1 t) t1) (getDLoc e) 
    let cs1 = s2 `composeSubst` s1
    (s3, es') <- typeCheckExps id (apply cs1 env) es ts
    return (s3 `composeSubst` cs1, e':es')
-- typeCheckExps id env e t = trace ("Non-exhaustive patterns" ++ show e ++ show t) $ return (nullSubst, [])

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
tiExp env (ExpId id (Field [])) = do
    case find id env of
        Just (Scheme _ t) -> return (nullSubst, t, ExpId id (Field []))
        Nothing -> do
            t <- newSPLVar
            dictate (refBeforeDec "Variable:" id) >> return (nullSubst, t, ExpId id (Field []))
tiExp (TypeEnv env) (ExpId id (Field fields)) = case Map.lookup id env of
    Just (Scheme ids t,s)  -> do
        (s1, t', ret) <- getType t fields
        return (s1, ret, ExpId id (Field fields))
    Nothing -> do
        t <- newSPLVar
        dictate (refBeforeDec "id: " id) >> return (nullSubst, t, ExpId id (Field fields))
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
tiExp env (ExpTuple locA (e1, e2) locB Nothing ) = do
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
    (s1, t, funCall') <- tiFunCall env funCall
    return (s1, t, ExpFunCall locA funCall' locB)

tiFunction (TypeEnv env) (ExpFunction locA id locB _) = 
    case Map.lookup id env of
        Just (scheme,_) -> do
            t <- instantiate scheme
            return (nullSubst, t, ExpFunction locA id locB (Just t))
        Nothing -> do
            t <- newSPLVar
            dictate (refBeforeDec "Function" id) >> return (nullSubst, t,ExpFunction locA id locB Nothing)

tiFunCall :: TypeEnv -> FunCall -> TI (Subst, SPLType, FunCall)
tiFunCall (TypeEnv env) (FunCall id args Nothing) = 
    case Map.lookup id env of
        Just (OverScheme lockedvars lockedType ops funcs,GlobalScope) -> do
            t <- instantiate (OverScheme lockedvars lockedType ops funcs)
            let argTypes = getArgsTypes t
            (s1, args') <- typeCheckExps id (TypeEnv env) args (init argTypes)
            let returnType = last argTypes
            return (s1, apply s1 returnType, FunCall id args' (Just $ apply s1 t))
        Just (scheme,GlobalScope) -> do
            t <- instantiate scheme
            let argTypes = getArgsTypes t
            (s1, args') <- typeCheckExps id (TypeEnv env) args (init argTypes)
            let returnType = last argTypes
            return (s1, apply s1 returnType, FunCall id args' (Just $ apply s1 t))
        Just (scheme,_) -> do
            t <- newSPLVar
            dictate (applVarAsFunc id ) >> return (nullSubst, t, FunCall id args Nothing)
        Nothing -> do
            t <- newSPLVar
            dictate (refBeforeDec "Function:" id) >> return (nullSubst, t, FunCall id args Nothing)



-- ===================== Helper functions ============================
isComplexType :: SPLType -> Bool
isComplexType ArrayType {} = True
isComplexType TupleType {} = True
isComplexType _ = False

isOrd :: Op2 -> Bool 
isOrd Leq = True
isOrd Geq = True
isOrd Le = True
isOrd Ge = True
isOrd _ = False

getFuncTypes :: [FunDecl] -> TI [(IDLoc, SPLType, Scope)]
getFuncTypes [] = return []
getFuncTypes ((FunDecl funName args (Just fType) vars stmts):xs) = do
    fTypes <- getFuncTypes xs
    return $ (funName, fType, GlobalScope):fTypes
getFuncTypes ((FunDecl funName args Nothing vars stmts):xs) = do
    argTypes <- replicateM (length args) newSPLVar
    retType <- newSPLVar
    let fType = if not (Prelude.null argTypes) then foldr1 FunType (argTypes ++ [retType]) else retType
    fTypes <- getFuncTypes xs
    return $ (funName, fType, GlobalScope):fTypes

getType :: SPLType -> [StandardFunction] -> TI (Subst, SPLType, SPLType)
getType t [] = do
    tv <- newSPLVar
    return (nullSubst, tv, tv)
getType t [Head locA locB] = do
    tv <- newSPLVar
    let t' = ArrayType (getFstLoc t) tv (getSndLoc t)
    s1 <- mgu t t'
    return (s1, apply s1  t', tv)
getType t [Tail loc _] = case t of
    TupleType _ (a, b) _ -> do
        return(nullSubst, t, b)
    _ -> do
        tv <- newSPLVar
        let t' = ArrayType (getFstLoc t) tv (getSndLoc t)
        s1 <- mgu t t'
        return (s1, apply s1 t', t')
getType t [Fst loc _] = case t of
    TupleType _ (a, b) _ -> do
        return(nullSubst, t, a)
    _ -> do
        a <- newSPLVar
        b <- newSPLVar
        let t' = TupleType (getFstLoc t) (a, b) (getSndLoc t)
        s1 <- mgu t t'
        return (s1, apply s1 t', apply s1 a)
getType t [Snd loc _] = do
    a <- newSPLVar
    b <- newSPLVar
    let t' = TupleType (getFstLoc t) (a, b) (getSndLoc t)
    s1 <- mgu t t'
    return (s1, apply s1  t', b)
getType t (x:xs) = do
    (s1, t', ret) <- getType t [x]
    (s2, t'', ret') <- getType ret xs
    let cs1 = s2 `composeSubst` s1
    let s3 = applySubst s2 s1
    return (s3, apply s3 t, ret')

op2Type :: Op2 -> ErrorLoc -> ErrorLoc -> TI (SPLType, SPLType, SPLType, SPLType)
op2Type x e1loc e2loc | x == Plus || x == Min || x == Mult || x == Div || x == Mod = do
    let e1T = TypeBasic (getFstLoc e1loc) BasicInt (getSndLoc e1loc)
    let e2T = TypeBasic (getFstLoc e2loc) BasicInt (getSndLoc e2loc)
    
    let retType = TypeBasic defaultLoc  BasicInt defaultLoc
    return (e1T, e2T, retType, FunType e1T (FunType e2T retType))
op2Type x e1loc e2loc | x == Eq || x == Neq = do
    tv <- newSPLVar

    let t = TypeBasic defaultLoc BasicBool defaultLoc
    return (tv, tv, t, FunType tv (FunType tv t))
op2Type x e1loc e2loc | x == Le || x == Ge || x == Leq || x == Geq  = do
    tv <- newSPLVarLoc (getFstLoc e1loc)

    let t = TypeBasic defaultLoc BasicBool defaultLoc
    return (tv, tv, t, FunType tv (FunType tv t))
op2Type x e1loc  e2loc | x== And || x == Or = do
    let e1T = TypeBasic (getFstLoc e1loc) BasicBool (getSndLoc e1loc)
    let e2T = TypeBasic (getFstLoc e2loc) BasicBool (getSndLoc e2loc)

    let t = TypeBasic defaultLoc BasicBool defaultLoc
    return (e1T, e2T, t, FunType e1T (FunType e2T t))
op2Type Con e1loc e2loc = do
    e1T <- newSPLVarLoc (getFstLoc e1loc)

    let e2T = ArrayType (getFstLoc e1loc) e1T (getFstLoc e1loc)
    let t = ArrayType defaultLoc e1T defaultLoc
    return (e1T, e2T, t, FunType e1T (FunType e2T t))

-- ===================== Overloading ============================
overloadFunction :: [IDLoc] -> SPLType -> TypeEnv -> [(Op2Typed,IDLoc,SPLType)] -> [(FunCall,IDLoc,SPLType)] -> ([IDLoc], SPLType, Scheme)
overloadFunction args fType env ops funcs = do
    let (ops', argsOps, typeOps) = combine ops 
    let (funcs', argsFuncs, typeFuncs) = combine funcs
    let args' = args ++ argsOps ++ argsFuncs
    let fType' = 
                let typesOfArgs = getArgsTypes fType 
                in foldr1 FunType (init typesOfArgs ++ typeOps ++ typeFuncs ++ [last typesOfArgs] )
    let scheme = 
            let Scheme xs t = generalize env fType' 
            in OverScheme xs t ops' funcs'
    (args', fType', scheme)
    where 
        combine (x:xs) = (\(a,b,c) (as,bs,cs) -> (a:as,b:bs,c:cs)) x (combine xs)
        combine [] = ([],[],[])



overloadedTypeName :: String -> SPLType -> String
overloadedTypeName start t = '_':start ++ typeToName t

overloadedOpName :: Op2 -> SPLType -> String
overloadedOpName op t = '_':op2String op ++ typeToName t

typeToName :: SPLType -> String 
typeToName (TypeBasic _ x _) = pp x
typeToName (TupleType _ (t1,t2) _) = "Tuple" ++ typeToName t1 ++ typeToName t2
typeToName (ArrayType _ a1 _) = "Array"++ typeToName a1
typeToName (FunType arg f) = "Func"
typeToName (Void _ _) = "Void"
typeToName (IdType id) = pp id

op2String :: Op2 -> String
op2String Le  = "lt"
op2String Ge  = "gt"
op2String Leq = "le"
op2String Geq = "ge"
op2String Eq  = "eq"
op2String Neq = "ne"

class Monomorphization a where
    monomorphize :: a -> TI (a, [(Op2Typed,IDLoc,SPLType)], [(FunCall, IDLoc, SPLType)])

instance Monomorphization a => Monomorphization [a] where
    monomorphize [] = pure ([],[],[])
    monomorphize (x:xs) = do
        (a,b,c) <- monomorphize x
        (as,b',c') <- monomorphize xs
        return (a:as,b++b',c++c')

instance Monomorphization FunDecl where
    monomorphize (FunDecl funName args fType vars stmts) = do
        (vars', ops, funcs) <- monomorphize vars 
        (stmts', ops', funcs') <- monomorphize stmts
        return (FunDecl funName args fType vars' stmts', ops++ops', funcs++funcs')

instance Monomorphization Stmt where
    monomorphize (StmtIf e stmts (Just els) loc) = do
        (e', ops, funcs) <- monomorphize e
        (stmts', ops1, funcs1) <- monomorphize stmts
        (els', ops2, funcs2) <- monomorphize els
        return (StmtIf e' stmts' (Just els') loc, ops++ops1++ops2, funcs++funcs1++funcs2)
    monomorphize (StmtIf e stmts Nothing loc) = do
        (e', ops, funcs) <- monomorphize e
        (stmts', ops1, funcs1) <- monomorphize stmts
        return (StmtIf e stmts Nothing loc, ops++ops1, funcs++funcs1)
    monomorphize (StmtWhile e stmts loc) = do
        (e', ops, funcs) <- monomorphize e
        (stmts', ops1, funcs1) <- monomorphize stmts
        return (StmtWhile e' stmts' loc, ops++ops1, funcs++funcs1)
    monomorphize (StmtAssignVar id fields e t) = do
        (e', ops, funcs) <- monomorphize e
        return (StmtAssignVar id fields e' t, ops, funcs)
    monomorphize (StmtFuncCall funCall loc) = do
        (funCall', ops, funcs) <- monomorphize funCall
        return (StmtFuncCall funCall' loc, ops, funcs)
    monomorphize (StmtReturn (Just e) loc) = do
        (e', ops, funcs) <- monomorphize e
        return (StmtReturn (Just e') loc, ops, funcs)

instance Monomorphization VarDecl where
    monomorphize (VarDeclType t id e) = do
        (e', ops, funcs) <- monomorphize e
        return (VarDeclType t id e',ops, funcs)

instance Monomorphization Exp where
-- findReplaceOLExp :: Exp -> TI (Exp, [(Op2Typed,IDLoc,SPLType)],[(FunCall,IDLoc,SPLType)])
    monomorphize (ExpOp2 locA e1 (Op2 op (Just t) loc) e2 locB) | containsIDType t = do
        let name = idLocCreator $ overloadedOpName op t
        (e1',ops1,funcs1) <- monomorphize e1
        (e2',ops2,funcs2) <- monomorphize e2
        let exp = ExpFunCall locA (FunCall name [e1',e2'] (Just t)) locB
        -- undefined 
        return (exp,(Op2 op (Just t) loc, name, t):(ops1++ops2),funcs1++funcs2)
    monomorphize (ExpFunCall locA funCall locB) = do
        (funCall', ops, funcs) <- monomorphize funCall
        return (ExpFunCall locA funCall' locB, ops, funcs)

instance Monomorphization FunCall where
-- findReplaceOLFunCall :: FunCall -> TI (FunCall, [(Op2Typed,IDLoc,SPLType)], [(FunCall, IDLoc, SPLType)])
    monomorphize (FunCall (ID idLocA "print" idLocB) args (Just t)) | containsIDType t = do
        let name = overloadedTypeName "print" t
        (args',ops,funcs) <- monomorphize args
        return 
            (FunCall (ID idLocA "print" idLocB) args' (Just t), 
            ops, 
            (FunCall (ID idLocA "print" idLocB) args' (Just t),ID defaultLoc name defaultLoc,t):funcs)


combineOverFuncs x y = do
    (a,b) <- x
    (c,d) <- y
    return (a++c,b++d)

containsIDType :: SPLType -> Bool
containsIDType (Void _ _) = False
containsIDType TypeBasic {} = False
containsIDType (IdType _) = True
containsIDType (TupleType _ (t1, t2) _) = containsIDType t1 || containsIDType t2
containsIDType (ArrayType _ a1 _) = containsIDType a1
containsIDType (FunType arg f) = containsIDType arg || containsIDType f

-- ===================== Error (Injection) ============================
injectErrLoc :: a -> TI a -> ErrorLoc  -> TI a
injectErrLoc def runable loc = case runTI runable of
    (That a, state) -> return a
    (These errs a, state) -> dictate errs >> return a
    (This (Error _ msg), state) -> confess (ErrorD loc msg) >> return def
    (This (ErrorD _ msg), state) -> confess (ErrorD loc msg) >> return def
    (This (Errors (ErrorD _ msg:xs)), state) -> confess (Errors (ErrorD loc msg:xs)) >> return def

injectErrLocMsg :: a -> TI a -> ErrorLoc -> String -> TI a
injectErrLocMsg def runable loc m = case runTI runable of
    (That a, state) -> return a
    (These errs a, state) -> runable
    (This (Error _ _), state) -> dictate (ErrorD loc m) >> return def
    (This (ErrorD _ _), state) -> dictate (ErrorD loc m) >> return def
    (This (Errors (ErrorD _ _:xs)), state) -> dictate (Errors (ErrorD loc m:xs)) >> return def

injectErrMsgAddition :: a -> TI a -> ErrorLoc -> String -> TI a
injectErrMsgAddition def runable loc m = case runTI runable of
    (That a, state) -> return a
    (These errs a, state) -> runable
    (This (Error _ msg), state) -> dictate (ErrorD loc (m++" "++msg)) >> return def
    (This (ErrorD _ msg), state) -> dictate (ErrorD loc (m++" "++msg)) >> return def
    (This (Errors (ErrorD _ msg:xs)), state) -> dictate (Errors (ErrorD loc (m++" "++msg):xs)) >> return def

lookupKey :: Ord a => a -> Map a b -> Maybe (b,a)
lookupKey a dict =
    case Map.lookup a dict of
        Just b -> Just (b, fst $ Map.elemAt (Map.findIndex a dict) dict)
        Nothing -> Nothing 

isGoodScope :: Scope -> IDLoc  -> TypeEnv -> Bool
isGoodScope s id (TypeEnv env) = 
    case Map.lookup id env of
        Just(scheme,scope) -> s==scope
        Nothing -> True

-- ===================== Standard Lib Functions ============================
stdLib :: TI TypeEnv
stdLib = do
    let env = TypeEnv Map.empty
    t1 <- newSPLVar
    let isEmptyType = FunType (ArrayType defaultLoc t1 defaultLoc) (TypeBasic defaultLoc BasicBool defaultLoc)
    let env' = TI.insert env (idLocCreator "isEmpty") (generalize env isEmptyType) GlobalScope

    t2 <- newSPLVar
    let printType = FunType t2 (Void defaultLoc defaultLoc)
    let env'' = TI.insert env' (idLocCreator "print") (generalize env' printType) GlobalScope
    return env''

-- ===================== Printing ============================
printEnv :: [(IDLoc, (Scheme,Scope))] -> String
printEnv [] = ""
printEnv ((ID _ id _,(Scheme _ t,GlobalScope)):xs) = id ++" :: " ++ pp t ++ " Global\n"++ printEnv xs
printEnv ((ID _ id _,(Scheme _ t,LocalScope)):xs) = id ++" :: " ++ pp t ++ " Local\n"++ printEnv xs


printSubst :: [(IDLoc,SPLType)] -> String
printSubst [] = ""
printSubst ((ID _ id _,t):xs) = id ++ " -> " ++ pp t ++ "\n"++ printSubst xs

-- ===================== Main Type Inference ============================
typeInference :: SPL -> Either Error (Subst, TypeEnv, SPL)
typeInference code = do
    case runTI (tiSPL code) of
        (That (s1, env, SPL code'), state) -> do
            cleanCode <- removeDeadCode (SPL $ removeMutRec code')
            let updatedCode = apply s1 cleanCode
            Right (s1, env, updatedCode)
        (These errs a, state) -> Left errs
        (This errs, state) -> Left errs

instance Types SPL where
    apply s (SPL []) = SPL []
    apply s (SPL x)  = SPL $ apply s x
    ftv = undefined

instance Types Decl where
    apply s (VarMain varDecl)   = VarMain $ apply s varDecl
    apply s (FuncMain funDecl)   = FuncMain $ apply s funDecl
    apply s (MutRec x)   = trace ("Error in apply on Mutrec\n" ++ pp (MutRec  x)) undefined
    ftv = undefined

instance Types VarDecl where
    apply s (VarDeclType t (ID id loc loc') e) = VarDeclType (apply s t) (ID id loc loc') e
    apply s e = e
    ftv = undefined

instance Types FunDecl where
    apply s (FunDecl funName args funType varDecls stmts) = do
        let varDecls' = apply s varDecls
        let stmts' = apply s stmts
        FunDecl funName args funType varDecls' stmts'
    ftv = undefined

instance Types Stmt where
    apply s (StmtIf e stmts Nothing loc) = do
        let e' = apply s e
        let stmts' = apply s stmts
        StmtIf e' stmts' Nothing loc
    apply s (StmtIf e stmts (Just els) loc) = do
        let e' = apply s e
        let stmts' = apply s stmts 
        let els' = apply s els
        StmtIf e' stmts' (Just els') loc
    apply s (StmtAssignVar id fields e typ) = do
        let e' = apply s e
        StmtAssignVar id fields e' (apply s typ)
    apply s (StmtFuncCall fCall loc) = do
        let fCall' = apply s fCall
        StmtFuncCall fCall' loc
    apply s (StmtReturn (Just e) loc) = do
        let e' = apply s e
        StmtReturn (Just e') loc
    apply s e = e
    ftv = undefined

instance Types Exp where
    apply s (ExpOp2 locA e1 (Op2 op (Just t) loc) e2 locB) = do
        let t' = apply s t
        let e1' = apply s e1
        let e2' = apply s e2
        ExpOp2 locA e1' (Op2 op (Just t') loc) e2' locB
    apply s (ExpFunCall locA fCall locB) =  do
        let fCall' = apply s fCall
        ExpFunCall locA fCall' locB
    apply s (ExpList locA es locB typ) = do
        let es' = apply s es
        ExpList locA es' locB (apply s typ) 
    apply s (ExpTuple locA (e1, e2) locB typ) = do
        let e1' = apply s e1
        let e2' = apply s e2
        ExpTuple locA (e1', e2') locB (apply s typ)
    apply s (ExpBracket e) = ExpBracket (apply s e)
    apply s (ExpOp1 locA op e locB) = let e' = apply s e in ExpOp1 locA op e' locB
    apply s e = e
    ftv = undefined

instance Types FunCall where
    apply s (FunCall (ID locA name locB) es (Just t)) = do
        let es' = apply s es
        FunCall (ID locA name locB) es' (Just $ apply s t)
    apply s (FunCall id es Nothing) = FunCall id es Nothing
    ftv = undefined



mainTIIO filename = do
    -- path <- getCurrentDirectory
    -- print path
    file <- readFile  ("../SPL_test_code/" ++ filename)
    case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
        Right (s1, TypeEnv env, code) -> do
            putStr $ pp code
            putStr $ "\nEnv:\n" ++ printEnv (Map.toList env)
            putStr $ "\nSubst:\n" ++ printSubst (Map.toList s1)
        Left x -> putStr $ showError file x


eq = FunDecl (ID (Loc 6 1) "equal" (Loc 6 6)) [ID (Loc 6 7) "x" (Loc 6 8),ID (Loc 6 10) "y" (Loc 6 11)] Nothing [] [StmtReturn (Just (ExpOp2 (Loc 7 14) (ExpId (ID (Loc 7 12) "x" (Loc 7 13)) (Field [])) (Op2 Eq Nothing (Loc 7 14)) (ExpId (ID (Loc 7 17) "y" (Loc 7 18)) (Field [])) (Loc 7 16))) (Loc 7 5)]

tiObject = do
    -- path <- getCurrentDirectory
    -- print path
    case runTI (tiFunDecl (TypeEnv Map.empty) eq) of
        (That (s1, TypeEnv env, code),_) -> do
            print code
            putStr "\n\n"
            putStr $ pp code
            putStr $ "\nEnv:\n" ++ printEnv (Map.toList env)
            putStr $ "\nSubst:\n" ++ printSubst (Map.toList s1)
        (This x,_) -> print x
        (These x _,_) -> print x


mainTI filename = do
    -- path <- getCurrentDirectory
    -- print path
    file <- readFile  ("../SPL_test_code/" ++ filename)
    case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
        Right (s1, TypeEnv env, code) -> do
            writeFile "../SPL_test_code/ti-out.spl"$ pp code
            putStr $ "\nEnv:\n" ++ printEnv (Map.toList env)
            putStr $ "\nSubst:\n" ++ printSubst (Map.toList s1)
        Left x -> putStr $ showError file x