module TI where

import Error
import Lexer
import AST
import Parser
import MutRec

import Data.Map as Map
import Data.Set as Set
import Data.Maybe

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import System.Exit
import System.Directory

import Debug.Trace

-- ===================== Type inference data types ============================

-- data TIEnv = TIEnv  {}
--     deriving(Show)
    
type TIState = Int
type TI a = ExceptT Error (State TIState) a

runTI :: TI a -> (Either Error a, TIState)
runTI t = runState (runExceptT t) initTIState
  where initTIState = 0

-- ===================== TypeEnv ============================
newtype TypeEnv = TypeEnv (Map IDLoc Scheme)
    deriving (Show)


insert :: TypeEnv -> IDLoc -> Scheme -> TypeEnv
insert (TypeEnv env) id scheme = TypeEnv (Map.insert id scheme env)

insertID :: TypeEnv -> IDLoc -> SPLType -> TypeEnv
insertID (TypeEnv env) id t = TypeEnv (Map.insert id (Scheme [] t) env)

insertMore :: TypeEnv -> [(IDLoc,SPLType)] -> TypeEnv
insertMore env [] = env
insertMore (TypeEnv env) [(id,t)] = TypeEnv (Map.insert id (Scheme [] t) env)
insertMore (TypeEnv env) ((id,t):xs) = insertMore (TypeEnv (Map.insert id (Scheme [] t) env)) xs

remove :: TypeEnv -> IDLoc -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

find :: IDLoc -> TypeEnv -> Maybe Scheme
find id (TypeEnv env) = Map.lookup id env

generalize :: TypeEnv -> SPLType -> Scheme
generalize env t  = Scheme vars t
  where vars = Set.toList (ftv t Set.\\ ftv env)

-- ===================== Scheme ============================
data Scheme = Scheme [IDLoc] SPLType
    deriving (Show, Eq)

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
    ftv (TypeEnv env)      =  ftv (Map.elems env)
    apply s (TypeEnv env)  =  TypeEnv (Map.map (apply s) env)

instance Types Scheme where
    ftv (Scheme vars t) = ftv t Set.\\ Set.fromList vars
    apply s (Scheme vars t) = Scheme vars (apply (Prelude.foldr Map.delete s vars) t)

instance Types SPLType where
    ftv (Void _) = Set.empty
    ftv (TypeBasic x _) = Set.empty
    ftv (TupleType (x,y) _) = ftv x `Set.union` ftv y
    ftv (ArrayType x _) = ftv x
    ftv (FunType args ret) = ftv args `Set.union` ftv ret
    ftv (IdType x _) = Set.singleton x
    apply s (IdType x t) = case Map.lookup x s of
                        Just t -> t
                        Nothing -> IdType x t
    apply s (FunType args ret) = FunType (apply s args) (apply s ret)
    apply s (TupleType (x,y) loc) = TupleType (apply s x, apply s y) loc
    apply s (ArrayType x loc) = ArrayType (apply s x) loc
    apply _ x = x

instance Types a =>  Types (Maybe a) where
    ftv (Just a) = ftv a
    ftv Nothing = Set.empty 
    apply s (Just a) = Just $ apply s a
    apply s Nothing = Nothing

newSPLVarWithClass :: Class -> TI SPLType
newSPLVarWithClass c =
    do  s <- get
        put (s + 1)
        return $ IdType (idLocCreator (reverse (toTyVar s))) (Just c)
  where 
    toTyVar :: Int -> String
    toTyVar c | c < 26    =  [toEnum (97+c)]
              | otherwise = let (n, r) = c `divMod` 26
                            in toEnum (97+r) : toTyVar (n-1)

newSPLVar :: TI SPLType
newSPLVar =
    do  s <- get
        put (s + 1)
        return $ IdType (idLocCreator (reverse (toTyVar s))) Nothing
  where 
    toTyVar :: Int -> String
    toTyVar c | c < 26    =  [toEnum (97+c)]
              | otherwise = let (n, r) = c `divMod` 26
                            in toEnum (97+r) : toTyVar (n-1)

instantiate :: Scheme -> TI SPLType
instantiate (Scheme vars t) = do  nvars <- mapM (const newSPLVar) vars
                                  let s = Map.fromList (zip vars nvars)
                                  return $ apply s t

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

instance MGU SPLType where
    mgu (TypeBasic x _) (TypeBasic y _) | x == y = return nullSubst
    mgu (TypeBasic x loc) (TypeBasic y loc') =  throwError $ generateError (TypeBasic x loc) (TypeBasic y loc')
    
    mgu (Void _) (Void _) = return nullSubst
    
    mgu (TupleType (l1,r1) _) (TupleType (l2,r2) _) = do 
        s1 <- mgu l1 l2
        s2 <- mgu r1 r2
        return (s1 `composeSubst` s2)
    mgu (ArrayType x _) (ArrayType y _) = mgu x y
    mgu (IdType id c) r = varBind id c r
    mgu l (IdType id c) = varBind id c l

    mgu (FunType arg ret) (FunType arg' ret') = do 
        s1 <- mgu arg arg'
        s2 <- mgu (apply s1 ret) (apply s1 ret')  
        return (s2 `composeSubst` s1)

    mgu t1 t2 =  throwError $ generateError t1 t2
    
    generateError t1 t2 = case getLoc t1 `compare` getLoc t2 of
        LT -> let (Loc line col) = getLoc t2 in Error line col ("Type "++ pp t1 ++" "++ showLoc t2 ++" does not unify with: " ++ pp t2)
        GT -> let (Loc line col) = getLoc t1 in Error line col ("Type "++ pp t1 ++" "++ showLoc t1 ++" does not unify with: " ++ pp t2 ++" "++ showLoc t2)
        EQ -> case getLoc t2 of 
                        (Loc (-1) (-1)) -> Error (-1) (-1) ("Types do not unify: " ++ pp t1 ++ " vs. " ++ pp t2)
                        (Loc line col) -> Error line col ("Type "++ pp t1 ++" "++ showLoc t1 ++" does not unify with: " ++ pp t2 ++" "++ showLoc t2)

varBind :: IDLoc -> Maybe Class -> SPLType -> TI Subst
varBind id _ (IdType t _) | id == t = return nullSubst
varBind id c (IdType t c') = return $ Map.singleton id (IdType t (composeClass c c'))
varBind id _ t | id `Set.member` ftv t = throwError $ Error (-1) (-1) ("occurs check fails: " ++ pp id ++ " vs. " ++ show t)
varBind id _ t = return $ Map.singleton id t

composeClass :: Maybe Class -> Maybe Class -> Maybe Class
composeClass Nothing c = c
composeClass c Nothing = c
composeClass c c' | c == c' = c
composeClass c c' | c /= c' = Just OrdClass

-- ===================== Type inference ============================
tiSPL :: TypeEnv -> SPL -> TI TypeEnv
tiSPL env (SPL [decl]) = do tiDecl env decl
tiSPL env (SPL (decl:decls)) = do 
            env' <- tiDecl env decl
            tiSPL env' (SPL decls)

tiDecl :: TypeEnv -> Decl -> TI TypeEnv
tiDecl env (VarMain x) = tiVarDecl env x
tiDecl env (FuncMain x) = snd <$> tiFunDecl env x

tiDecl env (MutRec funcs) = do
    fTypes <- getFuncTypes funcs
    let env' = insertMore env fTypes

    (s1,env'') <- tiFunDecls env' funcs

    generalizeFuncs env'' (Prelude.map fst fTypes)

getFuncTypes :: [FunDecl] -> TI [(IDLoc, SPLType)]
getFuncTypes [] = return []
getFuncTypes ((FunDecl funName args (Just fType) vars stmts):xs) = do
    fTypes <- getFuncTypes xs
    return $ (funName, fType):fTypes
getFuncTypes ((FunDecl funName args Nothing vars stmts):xs) = do
    argTypes <- replicateM (length args) newSPLVar
    retType <- newSPLVar
    let fType = if not (Prelude.null argTypes) then foldr1 FunType (argTypes ++ [retType]) else retType
    fTypes <- getFuncTypes xs
    return $ (funName, fType):fTypes

generalizeFuncs :: TypeEnv -> [IDLoc] -> TI TypeEnv
generalizeFuncs env [] = return env
generalizeFuncs (TypeEnv env) (x:xs) = case Map.lookup x env of
    Just (Scheme _ t) -> let scheme = generalize (TypeEnv env) t in
        generalizeFuncs (TypeEnv $ Map.insert x scheme env) xs
    _ -> throwError $ Error (getLineNum x) (getColNum x) ("Function " ++ pp x ++  " is mutual recursive and should therefore be in the type environment but it is not.")

tiVarDecls :: TypeEnv -> [VarDecl] -> TI TypeEnv
tiVarDecls env [] = return env
tiVarDecls env [decl] = do tiVarDecl env decl
tiVarDecls env (varDecl:varDecls) = do 
    env' <- tiVarDecl env varDecl
    tiVarDecls env' varDecls

tiVarDecl :: TypeEnv -> VarDecl -> TI TypeEnv
tiVarDecl (TypeEnv env) (VarDeclVar id e) = case Map.lookup id env of
    Just x -> throwError $ doubleDef id
    Nothing -> do
        (s1, t1) <- tiExp (TypeEnv env) e
        let scheme = Scheme [] t1
        let env' = TypeEnv (Map.insert id scheme env)
        return $ apply s1 env'
tiVarDecl (TypeEnv env) (VarDeclType t id e) = case Map.lookup id env of
    Just x -> throwError $ doubleDef id
    Nothing -> do
        (s1, t1) <- tiExp (TypeEnv env) e
        s2 <- mgu (apply s1  t) t1
        let cs1 = s2 `composeSubst` s1
        let t' = Scheme [] t1
        let env' = TypeEnv (Map.insert id t' env)
        return $ apply cs1 env'

tiFunDecls :: TypeEnv -> [FunDecl] -> TI (Subst, TypeEnv)
tiFunDecls env [] = return (nullSubst, env)
tiFunDecls (TypeEnv env) ((FunDecl funName args (Just funType) vars stmts):xs) = do
    let (argTypes, retType) = let a = getArgsTypes funType in (init a, last a)
    let env' = insertMore (TypeEnv env) (zip args argTypes) -- With this function + args inserted
    
    (s1,t1) <- tiStmts env' stmts
    
    let t1' = fromMaybe (Void defaultLoc) t1
    s2 <- mgu (apply s1 t1') retType

    let cs1 = s2 `composeSubst` s1

    (s3,env'') <- tiFunDecls (apply cs1 (TypeEnv env)) xs
            
    let cs2 = s3 `composeSubst` cs1

    return (cs2, apply cs2 env'')
tiFunDecls (TypeEnv env) ((FunDecl funName args Nothing vars stmts):xs) = do
    case Map.lookup funName env of
        Just (Scheme [] funType) -> do
            let (argTypes, retType) = let a = getArgsTypes funType in (init a, last a)
            let env' = insertMore (TypeEnv env) (zip args argTypes) -- With this function + args inserted
            
            (s1,t1) <- tiStmts env' stmts
            
            let t1' = fromMaybe (Void defaultLoc) t1
            s2 <- mgu (apply s1 t1') retType

            let cs1 = s2 `composeSubst` s1

            (s3,env'') <- tiFunDecls (apply cs1 (TypeEnv env)) xs
            
            let cs2 = s3 `composeSubst` cs1

            return (cs2, apply cs2 env'')
        nothing -> throwError $ Error (getLineNum funName) (getColNum funName) "Function is mutual recursive and should therefore be in the type environment but it is not."

tiFunDecl :: TypeEnv -> FunDecl -> TI (Subst, TypeEnv)
tiFunDecl env (FunDecl funName args (Just funType) vars stmts) = do

    let (argTypes, retType) = let a = getArgsTypes funType in (init a, last a)


    case length args `compare` length argTypes of
        LT -> throwError $ funcCallLessArgs funName
        GT -> throwError $ funcCallMoreArgs funName
        EQ -> do 
            let env' = TI.insertID env funName funType -- With only this function inserted
            let env'' = insertMore env' (zip args argTypes) -- With this function + args inserted
            env''' <- tiVarDecls env'' vars -- With this function + args + local varDecls inserted

            (s1,t1) <- tiStmts env''' stmts

            let t1' = fromMaybe (Void defaultLoc) t1
            s2 <- mgu (apply s1 t1') retType

            let cs1 = s2 `composeSubst` s1

            let Just (Scheme _ funType') = find funName (apply cs1 env''')
            let func = generalize env funType'

            return (cs1, TI.insert env' funName func)

tiFunDecl env (FunDecl funName args Nothing vars stmts) = do
    argTypes <- replicateM (length args) newSPLVar
    retType <- newSPLVar
    let fType = if not (Prelude.null argTypes) then foldr1 FunType (argTypes ++ [retType]) else retType
    let env' = TI.insertID env funName fType -- With only this function inserted
    let env'' = insertMore env' (zip args argTypes) -- With this function + args inserted
    env''' <- tiVarDecls env'' vars -- With this function + args + local varDecls inserted

    (s1,t1) <- tiStmts env''' stmts

    let t1' = fromMaybe (Void defaultLoc) t1

    s2 <- mgu (apply s1 t1') retType
    let cs1 = s2 `composeSubst` s1

    let Just (Scheme _ funType') = find funName (apply cs1 env''')
    let func = generalize env funType'

    return (cs1, TI.insert env' funName func)




tiStmts :: TypeEnv -> [Stmt] -> TI (Subst, Maybe SPLType)
tiStmts env [e] = 
    -- trace ("Calling tiStmts with: \n\t" ++ show env ++ "\n\n\t" ++ show e ++ "\n") $
    tiStmt env e
tiStmts env (e:es) = 
    -- trace ("Calling tiStmts with: \n\t" ++ show env ++ "\n\n\t" ++ show (e:es) ++ "\n") $
    do
        (s1, t1) <- tiStmt env e
        (s2, retType) <- tiStmts (apply s1 env) es
        let cs1 = s2 `composeSubst` s1
        s3 <- mgu (apply cs1 t1) retType
        let cs2 = s3 `composeSubst` cs1
        return (cs2, retType)

tiStmt :: TypeEnv -> Stmt -> TI (Subst, Maybe SPLType)
tiStmt env (StmtIf e stmts (Just els) _) = do
    (s1, conditionType) <- injectErrLoc (tiExp env e) (getLoc e)
    s2 <- injectErrLocMsg (mgu conditionType (TypeBasic BasicBool defaultLoc)) (getLoc e) ("Given condition does not have type Bool " ++ showLoc e)
    let cs1 = s2 `composeSubst` s1
    (s3, retIf) <- tiStmts (apply cs1 env) stmts
    let cs2 = s3 `composeSubst` cs1
    (s4, retElse) <- tiStmts (apply cs2 env) els
    let cs3 = s4 `composeSubst`cs2
    s5 <- mgu (apply cs3 retIf) (apply cs3 retElse)
    let cs4 = s5 `composeSubst` cs3
    return (cs4, apply cs4 retIf)
tiStmt env (StmtIf e stmts els _) | els == Just [] || isNothing els = 
    -- trace (show $ getLoc e) $ 
    do
    (s1, conditionType) <- injectErrLoc (tiExp env e) (getLoc e)
    s2 <- injectErrLocMsg (mgu conditionType (TypeBasic BasicBool defaultLoc)) (getLoc e) ("Given condition does not have type Bool " ++ showLoc e)
    let cs1 = s2 `composeSubst` s1
    (s3, t2) <- tiStmts (apply cs1 env) stmts
    let cs2 = s3 `composeSubst` cs1
    return (cs2, apply cs2 t2)


tiStmt env (StmtWhile e stmts loc) = do
    (s1, conditionType) <- injectErrMsgAddition (tiExp env e) (getLoc e) "tiStmt while"
    s2 <- injectErrLocMsg (mgu conditionType (TypeBasic BasicBool defaultLoc)) (getLoc e) ("Given condition does not have type Bool " ++ showLoc e)
    let cs1 = s2 `composeSubst` s1
    (s3, t3) <- tiStmts (apply cs1 env) stmts
    let cs2 = s3 `composeSubst` cs1
    return (cs2, apply cs2 t3)

tiStmt (TypeEnv env) (StmtFuncCall (FunCall id e) _) = case Map.lookup id env of
    Just scheme -> do
        t <- instantiate scheme
        let argTypes = init $ getArgsTypes t
        s1 <- typeCheckExps id (TypeEnv env) e argTypes
        return (s1, Nothing)
    Nothing -> throwError $ refBeforeDec "Variable:" id

tiStmt env (StmtReturn Nothing _) = return (nullSubst, Just (Void defaultLoc))
tiStmt env (StmtReturn (Just exp) _) = do 
    (s1,t1) <- tiExp env exp
    return (s1, Just t1)

tiStmt (TypeEnv env) (StmtDeclareVar id (Field []) e) = case Map.lookup id env of
    Just (Scheme ids t) -> do
        (s1, t1) <- tiExp (TypeEnv env) e
        s2 <- mgu (apply s1 t) t1
        let cs1 = s2 `composeSubst` s1
        return (cs1, Nothing)
    Nothing -> throwError $ refBeforeDec "Variable:" id
tiStmt (TypeEnv env) (StmtDeclareVar id (Field fields) e) = case Map.lookup id env of
    Just (Scheme ids t) -> do
        (s1, t1) <- tiExp (TypeEnv env) e
        (s2, t', ret) <- getType t fields
        let cs1 = s2 `composeSubst` s1
        s3 <- mgu (apply cs1 ret) t1
        let cs2 = s3 `composeSubst` cs1
        s4 <- mgu (apply cs2 t') t
        let cs3 = s4 `composeSubst` cs2
        return (cs3, Nothing)
    Nothing -> throwError $ refBeforeDec "Variable:" id


injectErrLoc :: TI a -> Loc -> TI a
injectErrLoc runable (Loc line col) = case runTI runable of
    (Right x, state) -> return x
    (Left (Error _ _ msg), state) -> throwError $ Error line col msg

injectErrLocMsg :: TI a -> Loc -> String -> TI a
injectErrLocMsg runable (Loc line col) m = case runTI runable of
    (Right x, state) -> return x
    (Left (Error _ _ msg), state) -> throwError $ Error line col m

injectErrMsgAddition :: TI a -> Loc -> String -> TI a
injectErrMsgAddition runable (Loc line col) m = case runTI runable of
    (Right x, state) -> return x
    (Left (Error _ _ msg), state) -> throwError $ Error line col (m++" "++msg)

typeCheckExps :: IDLoc -> TypeEnv -> [Exp] -> [SPLType] -> TI Subst
typeCheckExps id env [] [] = return nullSubst
typeCheckExps id env [x] [] = throwError $ funcCallMoreArgs id
typeCheckExps id env [] [x] = throwError $ funcCallLessArgs id
typeCheckExps id env (e:es) (t:ts) =
    -- let ret = runTI (tiExp env e) in trace  (show t ++ "\n" ++ show ret ++ "\n\n") $
    do 
    (s1,t1) <- injectErrMsgAddition (tiExp env e) (getLoc e) "typeCheckExps"
    -- s2 <- injectErrLocMsg (mgu (apply s1 t) t1) (getLoc e) ("Argument '"++ pp e ++ "' should have type "++ pp t)
    s2 <- mgu (apply s1 t) t1
    let cs1 = s2 `composeSubst` s1
    s3 <- typeCheckExps id (apply cs1 env) es ts
    return $ s3 `composeSubst` cs1

tiExp :: TypeEnv -> Exp -> TI (Subst, SPLType)    
tiExp env (ExpId id (Field [])) = do
    case find id env of
        Just (Scheme _ t) -> return (nullSubst, t)
        Nothing -> throwError $ refBeforeDec "Variable:" id
tiExp (TypeEnv env) (ExpId id (Field fields)) = case Map.lookup id env of
    Just (Scheme ids t) -> do 
        (s1, t', ret) <- getType t fields
        return (s1, ret)
    Nothing -> throwError $ Error (getLineNum id) (getColNum id) ("id: '" ++ pp id ++ "', referenced " ++ showLoc id ++ ", has not been defined yet: (i.e. reference before declaration)")
tiExp _ (ExpInt i loc)  = return (nullSubst, TypeBasic BasicInt loc)
tiExp _ (ExpBool b loc) = return (nullSubst, TypeBasic BasicBool loc)
tiExp _ (ExpChar c loc) = return (nullSubst, TypeBasic BasicChar loc)
tiExp env (ExpBracket e) = tiExp env e
tiExp env (ExpList [] _) = do 
      tv <- newSPLVar
      return (nullSubst, ArrayType tv defaultLoc)
tiExp env (ExpEmptyList _) = do 
      tv <- newSPLVar
      return (nullSubst, ArrayType tv defaultLoc)
tiExp env (ExpList (x:xs) loc) = do
    (s1, t1) <- tiExp env x
    (s2, t2) <- tiExp (apply s1 env) (ExpList xs loc)
    return (s2 `composeSubst` s1, t2)
tiExp env (ExpTuple (e1, e2) loc) = do
    (s1, t1) <- tiExp env e1
    (s2, t2) <- tiExp (apply s1 env) e2
    let cs1 = s2 `composeSubst` s1
    return (cs1, apply cs1 (TupleType (t1,t2) defaultLoc))

tiExp env (ExpOp2 e1 op e2 loc) = do
    (t1,t2,t3) <- op2Type op
    (s1, t1') <- injectErrLoc (tiExp env e1) (getLoc e1)
    s2 <- injectErrLoc (mgu t1' (apply s1 t1)) (getLoc e1)
    let cs1 = s2 `composeSubst` s1
    (s3,t2') <- injectErrLoc (tiExp (apply cs1 env) e2) (getLoc e2)
    let cs2 = s3 `composeSubst` cs1
    s4 <- injectErrLoc (mgu (apply cs2 t2') (apply cs2  t2)) (getLoc e2)
    let cs3 = s4 `composeSubst` cs2 
    return (cs3, apply cs3 t3)

tiExp env (ExpOp1 op e _) = case op of
    Neg -> do 
        (s1, t1) <- tiExp env e
        s2 <- mgu t1 (TypeBasic BasicInt defaultLoc)
        return (s2 `composeSubst` s1, t1)
    Not -> do 
        (s1, t1) <- tiExp env e
        s2 <- mgu t1 (TypeBasic BasicBool defaultLoc)
        return (s2 `composeSubst` s1, t1)
tiExp (TypeEnv env) (ExpFunCall (FunCall name args) _) = case Map.lookup name env of
    Just scheme -> do 
        t <- instantiate scheme
        let argTypes = getArgsTypes t
        s1 <- typeCheckExps name (TypeEnv env) args (init argTypes)
        let returnType = last argTypes
        return (s1, apply s1 returnType)
    Nothing -> throwError $ refBeforeDec "Function:" name

getType :: SPLType -> [StandardFunction] -> TI (Subst, SPLType, SPLType)
getType t [] = do
    tv <- newSPLVar
    return (nullSubst, tv, tv)
getType t [Head loc] = do
    tv <- newSPLVar
    let t' = ArrayType tv defaultLoc
    s1 <- mgu t t'
    return (s1, apply s1  t', tv)
getType t [Tail loc] = case t of
    TupleType (a, b) _ -> do 
        return(nullSubst, t, b)
    _ -> do
        tv <- newSPLVar
        let t' = ArrayType tv defaultLoc
        let retType = ArrayType tv defaultLoc
        s1 <- mgu t t'
        return (s1, apply s1 t', t')
getType t [First loc] = case t of
    TupleType (a, b) _ -> do 
        return(nullSubst, t, a)
    _ -> do
        a <- newSPLVar
        b <- newSPLVar
        let t' = TupleType (a, b) defaultLoc
        s1 <- mgu t t'
        return (s1, apply s1 t', apply s1 a)
getType t [Second loc] = do
    a <- newSPLVar
    b <- newSPLVar
    let t' = TupleType (a, b) defaultLoc
    s1 <- mgu t t'
    return (s1, apply s1  t', b) 
getType t [IsEmpty loc] = do
    tv <- newSPLVar
    let t' = ArrayType tv defaultLoc
    let retType = TypeBasic BasicBool defaultLoc
    s1 <- mgu t t'
    return (s1, apply s1 t', retType)
getType t (x:xs) = do
    (s1, t', ret) <- getType t [x]
    (s2, t'', ret') <- getType ret xs
    let cs1 = s2 `composeSubst` s1
    let s3 = applySubst s2 s1
    return (s3, apply s3 t, ret')

op2Type :: Op2 -> TI (SPLType,SPLType,SPLType)
op2Type x | x == Plus || x == Min || x == Mult || x == Div || x == Mod = 
    return (TypeBasic BasicInt defaultLoc, TypeBasic BasicInt defaultLoc, TypeBasic BasicInt defaultLoc)
op2Type x | x == Eq || x == Neq = do
    tv <- newSPLVarWithClass EqClass 
    return (tv, tv, TypeBasic BasicBool defaultLoc)

op2Type x | x == Le || x == Ge || x == Leq || x == Geq  = do
    tv <- newSPLVarWithClass OrdClass 
    return (tv, tv, TypeBasic BasicBool defaultLoc)
op2Type x | x== And || x == Or = 
    return (TypeBasic BasicBool defaultLoc, TypeBasic BasicBool defaultLoc, TypeBasic BasicBool defaultLoc)
op2Type Con = do 
    tv <- newSPLVar
    return (tv, ArrayType tv defaultLoc, ArrayType tv defaultLoc)

-- ===================== Type Inference ============================

typeInference :: SPL -> Either Error SPL
typeInference (SPL code) = do
    case runTI (tiSPL (TypeEnv Map.empty) (SPL code)) of
        (Right env, _) -> Right $ updateTypes (SPL $ removeMutRec code) env 
        (Left x, _) -> Left x

typeInferenceEnv :: SPL -> Either Error TypeEnv
typeInferenceEnv (SPL code) = do
    case runTI (tiSPL (TypeEnv Map.empty) (SPL code)) of
        (Right env, _) -> Right env 
        (Left x, _) -> Left x


class UpdateTypes a where
    updateTypes :: a -> TypeEnv -> a

instance UpdateTypes a => UpdateTypes [a] where
    updateTypes [] env = []
    updateTypes (x:xs) env = updateTypes x env :updateTypes xs env

instance UpdateTypes SPL where
    updateTypes (SPL []) env = SPL []
    updateTypes (SPL x) env = SPL $ updateTypes x env

instance UpdateTypes Decl where
    updateTypes (VarMain varDec) env = VarMain $ updateTypes varDec env
    updateTypes (FuncMain funDecl) env = FuncMain $ updateTypes funDecl env
    updateTypes (MutRec x) env = MutRec $ updateTypes x env

instance UpdateTypes VarDecl where
    updateTypes (VarDeclVar id e) env = 
        let Just (Scheme _ varType) = find id env in
        VarDeclType varType id e
    updateTypes x env = x

instance UpdateTypes FunDecl where
    updateTypes (FunDecl funName args Nothing varDecls stmts) env = 
        let Just (Scheme _ funType) = find funName env in
        FunDecl funName args (Just funType) varDecls stmts
    updateTypes x env = x

mainTI filename = do
      -- path <- getCurrentDirectory
      -- print path
      file <- readFile  ("../SPL_test_code/" ++ filename)
      case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of 
            Right x -> do
                writeFile "../SPL_test_code/ti-out.spl"$ pp x
            Left x -> putStr $ show x ++ "\n" ++ showPlaceOfError file x



mainTIEnv filename = do
      -- path <- getCurrentDirectory
      -- print path
      file <- readFile  ("../SPL_test_code/" ++ filename)
      case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInferenceEnv of 
            Right x -> print x
            Left x -> putStr $ show x ++ "\n" ++ showPlaceOfError file x

-- instance PrettyPrinter SPL where