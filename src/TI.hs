module TI where

import Parser
import AST
import Lexer

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

-- ===================== TypeEnv ============================
newtype TypeEnv = TypeEnv (Map ID Scheme)
    deriving (Show)



insert :: TypeEnv -> ID -> SPLType -> TypeEnv
insert (TypeEnv env) id t = TypeEnv (Map.insert id (Scheme [] t) env)

insertMore :: TypeEnv -> [(ID,SPLType)] -> TypeEnv
insertMore (TypeEnv env) [(id,t)] =TypeEnv (Map.insert id (Scheme [] t) env)
insertMore (TypeEnv env) ((id,t):xs) = insertMore (TypeEnv (Map.insert id (Scheme [] t) env)) xs

remove :: TypeEnv -> ID -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

find :: ID -> TypeEnv -> Maybe SPLType
find id (TypeEnv env) = do 
    (Scheme _ t) <- Map.lookup id env
    return t

generalize :: TypeEnv -> SPLType -> Scheme
generalize env t  =   Scheme vars t
  where vars = Set.toList (ftv t Set.\\ ftv env)

-- ===================== Scheme ============================
data Scheme = Scheme [ID] SPLType
    deriving (Show, Eq)


-- ===================== ASPLType ============================
-- data ASPLType = ASPLType SPLType  
--              | AFunType FunType
--              | ARetType RetType
--              deriving (Eq, Show)
-- instance PrettyPrinter SPLType where
--     pp (ASPLType x) = pp x 
--     pp (AFunType x) = pp x
--     pp (ARetType x) = pp x
    
class Types a where
    ftv :: a -> Set ID 
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
    ftv Void = Set.empty
    ftv (TypeBasic x) = Set.empty
    ftv (TupleType (x,y)) = ftv x `Set.union` ftv y
    ftv (ArrayType x) = ftv x
    ftv (FunType args ret) = ftv args `Set.union` ftv ret
    ftv (IdType x _) = Set.singleton x
    apply s (IdType x t) = case Map.lookup x s of
                        Just t -> t
                        Nothing -> IdType x t
    apply s (FunType args ret) = FunType (apply s args) (apply s ret)
    apply s (TupleType (x,y)) = TupleType (apply s x, apply s y)
    apply s (ArrayType x) = ArrayType (apply s x)
    apply _ x = x

instance Types a =>  Types (Maybe a) where
    ftv (Just a) = ftv a
    ftv Nothing = Set.empty 
    apply s (Just a) = Just $ apply s a
    apply s Nothing = Nothing

-- ===================== Substitution ============================
type Subst = Map.Map ID SPLType

nullSubst :: Subst
nullSubst = Map.empty 

applySubst :: Subst -> Subst -> Subst
applySubst s1 = Map.map $ apply s1

composeSubst::Subst -> Subst -> Subst 
composeSubst s1 s2 = Map.map (apply s1) s2 `Map.union` s1

-- ===================== Type inference data types ============================

data TIEnv = TIEnv  {}
    deriving(Show)
    
type TIState = Int
type TI a = ExceptT ID (State TIState) a

runTI :: TI a -> (Either ID a, TIState)
runTI t = runState (runExceptT t) initTIState
  where initTIState = 0


-- newASPLVar :: TI SPLType
-- newASPLVar =
--     do  s <- get
--         put (s + 1)
--         return $ ASPLType (IdType (reverse (toTyVar s)))
--   where 
--     toTyVar :: Int -> String
--     toTyVar c | c < 26    =  [toEnum (97+c)]
--               | otherwise = let (n, r) = c `divMod` 26
--                             in toEnum (97+r) : toTyVar (n-1)

newSPLVarWithClass :: Class -> TI SPLType
newSPLVarWithClass c =
    do  s <- get
        put (s + 1)
        return $ IdType (reverse (toTyVar s)) (Just c)
  where 
    toTyVar :: Int -> String
    toTyVar c | c < 26    =  [toEnum (97+c)]
              | otherwise = let (n, r) = c `divMod` 26
                            in toEnum (97+r) : toTyVar (n-1)


newSPLVar :: TI SPLType
newSPLVar =
    do  s <- get
        put (s + 1)
        return $ IdType (reverse (toTyVar s)) Nothing
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
-- TODO Change TI stuff to Either
class MGU a where
    mgu :: a -> a -> TI Subst

instance MGU a => MGU [a] where
    mgu [] [] = return nullSubst
    mgu (x:xs) (y:ys) = do s1 <- mgu x y
                           s2 <- mgu xs ys
                           return (s1 `composeSubst` s2) 

instance MGU a => MGU (Maybe a) where
    mgu (Just l) (Just r) = mgu l r
    mgu Nothing _ = return nullSubst
    mgu _ Nothing = return nullSubst

-- instance MGU AllType where
--     mgu (AFunType l) (AFunType r) = do mgu l r
--     mgu (ASPLType l) (ASPLType r) = do mgu l r
--     mgu (ARetType l) (ARetType r) = do mgu l r
--     mgu t1 t2 =  throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

-- instance MGU FunType where
--     mgu (FunType xs retx) (FunType ys rety) = do s1 <- mgu xs ys
--                                                  s2 <- mgu (apply s1 retx) (apply s1 rety)  
--                                                  return (s1 `composeSubst` s2)

instance MGU SPLType where
    mgu (TupleType (l1,r1)) (TupleType (l2,r2)) = do s1 <- mgu l1 l2
                                                     s2 <- mgu r1 r2
                                                     return (s1 `composeSubst` s2)
    mgu (ArrayType x) (ArrayType y) = mgu x y
    mgu (TypeBasic x) (TypeBasic y) = mgu x y
    mgu (IdType id c) r = varBind id c r
    mgu l (IdType id c) = varBind id c l

    mgu Void Void = return nullSubst
    mgu (FunType args ret) (FunType args' ret') = do 
        s1 <- mgu args args'
        s2 <- mgu (apply s1 ret) (apply s1 ret')  
        return (s1 `composeSubst` s2)

    mgu t1 t2 =  throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

instance MGU BasicType where
    mgu a b | a == b = return nullSubst
    mgu t1 t2 =  throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

-- instance MGU RetType where
--     mgu Void Void = return nullSubst
--     mgu Void (RetSplType (IdType id)) = varBind id (ARetType Void)
--     mgu (RetSplType (IdType id)) Void = varBind id (ARetType Void)
--     mgu (RetSplType x) (RetSplType y) = mgu x y
--     mgu t1 t2 =  throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

varBind :: ID -> Maybe Class -> SPLType -> TI Subst
varBind id _ (IdType t _) | id == t = return nullSubst
varBind id c (IdType t c') = return $ Map.singleton id (IdType t (composeClass c c'))
varBind id _ t | id `Set.member` ftv t = throwError $ "occurs check fails: " ++ id ++ " vs. " ++ show t
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
tiDecl env (FuncMain x) = tiFunDecl env x
-- TODO implement MutRec
tiDecl env (MutRec []) = undefined 
tiDecl env (MutRec (x:xs)) = undefined 

tiVarDecls :: TypeEnv -> [VarDecl] -> TI TypeEnv
tiVarDecls env [] = return env
tiVarDecls env [decl] = do tiVarDecl env decl
tiVarDecls env (varDecl:varDecls) = do 
    env' <- tiVarDecl env varDecl
    tiVarDecls env' varDecls

tiVarDecl :: TypeEnv -> VarDecl -> TI TypeEnv
tiVarDecl (TypeEnv env) (VarDeclVar id e) = case Map.lookup id env of
    Just x -> throwError $ "Variable with name: '" ++ id ++ "', already exist in the type environment: (i.e. double decleration)"
    Nothing -> do
        --tv <- newASPLVar
        (s1, t1) <- tiExp (TypeEnv env) e
        -- let t' = generalize (apply s1 (TypeEnv env)) t1
        let scheme = Scheme [] t1
        let env' = TypeEnv (Map.insert id scheme env)
        -- s2 <- mgu (apply s1 t1) (ASPLType $ IdType id)
        return $ apply s1 env'
tiVarDecl (TypeEnv env) (VarDeclType t id e) = case Map.lookup id env of
    Just x -> throwError $ "Variable with name: '" ++ id ++ "', already exist in the type environment: (i.e. double decleration)"
    Nothing -> do
        (s1, t1) <- tiExp (TypeEnv env) e
        s2 <- mgu (apply s1  t) t1
        let cs1 = s2 `composeSubst` s1
        --let t' = generalize (apply cs1 (TypeEnv env)) t1
        let t' = Scheme [] t1
        let env' = TypeEnv (Map.insert id t' env)
        return $ apply cs1 env'


tiFunDeclTest :: TypeEnv -> FunDecl -> TI (Subst, Subst, Maybe SPLType, TypeEnv)
tiFunDeclTest env (FunDecl funName args (Just funType) vars stmts) = undefined
tiFunDeclTest env (FunDecl funName args Nothing vars stmts) = do
    argTypes <- replicateM (length args) newSPLVar
    retType <- newSPLVar
    let fType = if not (Prelude.null argTypes) then foldr1 FunType (argTypes ++ [retType]) else retType
    let env' = TI.insert env funName fType -- With only this function inserted
    let env'' = insertMore env' (zip args argTypes) -- With this function + args inserted
    env''' <- tiVarDecls env'' vars -- With this function + args + local varDecls inserted

    -- let (l,r) = Prelude.splitAt 2 stmts

    (s1,t1) <- tiStmts env''' stmts
    -- (s4,t4) <- tiStmts env''' r


    let t1' = fromMaybe Void t1

    s2 <- mgu retType (apply s1 t1')
    let cs1 = s2 `composeSubst` s1
    return (s1, s2, t1, apply cs1 env')
    -- return (cs1, apply cs1 env''')
    -- return (cs1,env'

tiFunDecl :: TypeEnv -> FunDecl -> TI TypeEnv
tiFunDecl env (FunDecl funName args (Just funType) vars stmts) = do

    let (argTypes, retType) = let a = getArgsTypes funType in (init a, last a)


    case length args `compare` length argTypes of
        LT -> throwError $ "Function: '" ++ funName ++ "'  has less arguments than it has types"
        GT -> throwError $ "Function: '" ++ funName ++ "'  has more arguments than it has types"
        EQ -> do 
            let env' = TI.insert env funName funType -- With only this function inserted
            let env'' = insertMore env' (zip args argTypes) -- With this function + args inserted
            env''' <- tiVarDecls env'' vars -- With this function + args + local varDecls inserted

            (s1,t1) <- tiStmts env''' stmts

            let t1' = fromMaybe Void t1

            s2 <- mgu (apply s1 t1') retType
            let cs1 = s2 `composeSubst` s1
            return $ apply s1 env'

tiFunDecl env (FunDecl funName args Nothing vars stmts) = do
    argTypes <- replicateM (length args) newSPLVar
    retType <- newSPLVar
    let fType = if not (Prelude.null argTypes) then foldr1 FunType (argTypes ++ [retType]) else retType
    let env' = TI.insert env funName fType -- With only this function inserted
    let env'' = insertMore env' (zip args argTypes) -- With this function + args inserted
    env''' <- tiVarDecls env'' vars -- With this function + args + local varDecls inserted

    (s1,t1) <- tiStmts env''' stmts

    let t1' = fromMaybe Void t1

    s2 <- mgu (apply s1 t1') retType
    let cs1 = s2 `composeSubst` s1
    return $ apply cs1 env'


getArgsTypes :: SPLType -> [SPLType]
getArgsTypes (FunType args ret) = getArgsTypes args ++ getArgsTypes ret
getArgsTypes x = [x]

-- tiStmtsTest :: TypeEnv -> [Stmt] -> TI (Subst, Maybe SPLType, TypeEnv)
-- tiStmtsTest env [e] = do 
--     (s1, t1) <- tiStmt env e
--     return (s1, t1, apply s1 env)
-- tiStmtsTest env (e:es) = do
--     (s1, t1) <- tiStmt env e
--     (s2, retType, env') <- tiStmtsTest env es
--     let cs1 = s2 `composeSubst` s1
--     s3 <- mgu t1 retType
--     let cs2 = s3 `composeSubst` cs1
--     return (cs2, retType, apply cs2 env)


tiStmts :: TypeEnv -> [Stmt] -> TI (Subst, Maybe SPLType)
tiStmts env [e] = trace ("Calling tiStmts with: \n\t" ++ show env ++ "\n\n\t" ++ show e ++ "\n") $ tiStmt env e
tiStmts env (e:es) = trace ("Calling tiStmts with: \n\t" ++ show env ++ "\n\n\t" ++ show (e:es) ++ "\n") $ do
    (s1, retType) <- tiStmts env es
    (s2, t1) <- tiStmt (apply s1 env) e
    let cs1 = s2 `composeSubst` s1
    s3 <- mgu (apply cs1 t1) retType
    let cs2 = s3 `composeSubst` cs1
    return (cs2, retType)

tiStmt :: TypeEnv -> Stmt -> TI (Subst, Maybe SPLType)
tiStmt env (StmtIf e stmts (Just els)) = do
    (s1, conditionType) <- tiExp env e
    s2 <- mgu conditionType (TypeBasic BasicBool)
    let cs1 = s2 `composeSubst` s1
    (s3, retIf) <- tiStmts (apply cs1 env) stmts
    let cs2 = s3 `composeSubst` cs1
    (s4, retElse) <- tiStmts (apply cs2 env) els
    let cs3 = s4 `composeSubst`cs2
    s5 <- mgu (apply cs3 retIf) (apply cs3 retElse)
    let cs4 = s5 `composeSubst` cs3
    return (cs4, apply cs4 retIf)
tiStmt env (StmtIf e stmts Nothing) = do
    (s1, conditionType) <- tiExp env e
    s2 <- mgu conditionType (TypeBasic BasicBool)
    let cs1 = s2 `composeSubst` s1
    (s3, t2) <- tiStmts (apply cs1 env) stmts
    let cs2 = s3 `composeSubst` cs1
    return (cs2, apply cs2 t2)

tiStmt env (StmtWhile e stmts) = do
    (s1, conditionType) <- tiExp env e 
    s2 <- mgu conditionType (TypeBasic BasicBool)
    let cs1 = s2 `composeSubst` s1
    (s3, t3) <- tiStmts (apply cs1 env) stmts
    let cs2 = s3 `composeSubst` cs1
    return (cs2, apply cs2 t3)

tiStmt env (StmtReturn Nothing) = return (nullSubst, Just Void)
tiStmt env (StmtReturn (Just exp)) = do 
    (s1,t1) <- tiExp env exp
    return (s1, Just t1)

tiStmt (TypeEnv env) (StmtDeclareVar id (Field []) e) = case Map.lookup id env of
    Just (Scheme ids t) -> do
        (s1, t1) <- tiExp (TypeEnv env) e
        s2 <- mgu (apply s1 t) t1
        let cs1 = s2 `composeSubst` s1
        return (cs1, Nothing)
    Nothing -> throwError $ "id: '" ++ id ++ "', does not exist in the type environment: (i.e. reference before declaration)"
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
    Nothing -> throwError $ "id: '" ++ id ++ "', does not exist in the type environment: (i.e. reference before declaration)"

tiExp :: TypeEnv -> Exp -> TI (Subst, SPLType)    
tiExp env (ExpId id (Field [])) = do
    case find id env of
        Just t -> return (nullSubst, t)
        Nothing -> throwError $ "id: '" ++ id ++ "', does not exist in the type environment: (i.e. reference before declaration)"
tiExp (TypeEnv env) (ExpId id (Field fields)) = case Map.lookup id env of
    Just (Scheme ids t) -> do 
        (s1, t', ret) <- getType t fields
        return (s1, ret)
    Nothing -> throwError $ "id: '" ++ id ++ "', does not exist in the type environment: (i.e. reference before declaration)"
tiExp _ (ExpInt i)  = return (nullSubst, TypeBasic BasicInt)
tiExp _ (ExpBool b) = return (nullSubst, TypeBasic BasicBool)
tiExp _ (ExpChar c) = return (nullSubst, TypeBasic BasicChar)
tiExp env (ExpBracket e) = tiExp env e
tiExp env x | x == ExpList [] || x == ExpEmptyList = do 
      tv <- newSPLVar
      return (nullSubst, ArrayType tv)
tiExp env (ExpList (x:xs)) = do
    (s1, t1) <- tiExp env x
    (s2, t2) <- tiExp (apply s1 env) (ExpList xs)
    return (s2 `composeSubst` s1, t2)
tiExp env (ExpTuple (e1, e2)) = do
    (s1, t1) <- tiExp env e1
    (s2, t2) <- tiExp (apply s1 env) e2
    let cs1 = s2 `composeSubst` s1
    return (cs1, apply cs1 (TupleType (t1,t2)))
tiExp env (ExpOp2 e1 op e2) = do
    (t1,t2,t3) <- op2Type op
    (s1, t1') <- tiExp env e1
    s2 <- mgu t1' (apply s1 t1)
    let cs1 = s1 `composeSubst` s2
    (s3,t2') <- tiExp (apply cs1 env) e2
    let cs2 = s3 `composeSubst` cs1
    s4 <- mgu (apply cs2 t2') (apply cs2  t2)
    let cs3 = s4 `composeSubst` cs2 
    return (cs3, apply cs3 t3)
tiExp env (ExpOp1 op e) = case op of
    Neg -> do 
        (s1, t1) <- tiExp env e
        s2 <- mgu t1 (TypeBasic BasicInt)
        return (s2 `composeSubst` s1, t1)
    Not -> do 
        (s1, t1) <- tiExp env e
        s2 <- mgu t1 (TypeBasic BasicBool)
        return (s2 `composeSubst` s1, t1)
tiExp (TypeEnv env) (ExpFunCall (FunCall name args)) = case Map.lookup name env of
    Just (Scheme ids t) -> do 
        let FunType arg ret = t
        return (nullSubst, ret)
    Nothing -> throwError $ "Function: '" ++ name ++ "', does not exist in the type environment: (i.e. reference before decleration)"

getType :: SPLType -> [StandardFunction] -> TI (Subst, SPLType, SPLType)
getType t [] = do
    tv <- newSPLVar
    return (nullSubst, tv, tv)
getType t [Head] = do
    tv <- newSPLVar
    let t' = ArrayType tv
    s1 <- mgu t t'
    return (s1, apply s1  t', tv)
getType t [Tail] = case t of
    TupleType (a, b) -> do 
        return(nullSubst, t, b)
    _ ->do
        tv <- newSPLVar
        let t' = ArrayType tv
        let retType = ArrayType tv
        s1 <- mgu t t'
        return (s1, apply s1  t', ArrayType tv)
getType t [First] = case t of
    TupleType (a, b) -> do 
        return(nullSubst, t, a)
    _ ->do
        a <- newSPLVar
        b <- newSPLVar
        let t' = TupleType (a, b)
        s1 <- mgu t t'
        return (s1, apply s1 t', apply s1 a)
getType t [Second] = do
    a <- newSPLVar
    b <- newSPLVar
    let t' = TupleType (a, b)
    s1 <- mgu t t'
    return (s1, apply s1  t', b)
getType t [IsEmpty] = do
    tv <- newSPLVar
    let t' = ArrayType tv
    let retType = TypeBasic BasicBool
    s1 <- mgu t t'
    return (s1, apply s1 t', TypeBasic BasicBool)
getType t (x:xs) = do
    (s1, t', ret) <- getType t [x]
    (s2, t'', ret') <- getType ret xs
    let cs1 = s2 `composeSubst` s1
    let s3 = applySubst s2 s1
    return (s3, apply s3 t, ret')

op2Type :: Op2 -> TI (SPLType,SPLType,SPLType)
op2Type x | x == Plus || x == Min || x == Mult || x == Div || x == Mod = 
    return (TypeBasic BasicInt, TypeBasic BasicInt, TypeBasic BasicInt)
op2Type x | x == Eq || x == Neq = do
    tv <- newSPLVarWithClass EqClass 
    return (tv, tv, TypeBasic BasicBool)

op2Type x | x == Le || x == Ge || x == Leq || x == Geq  = do
    tv <- newSPLVarWithClass OrdClass 
    return (tv, tv, TypeBasic BasicBool)
op2Type x | x== And || x == Or = 
    return (TypeBasic BasicBool, TypeBasic BasicBool, TypeBasic BasicBool)
op2Type Con = do 
    tv <- newSPLVar
    return (tv, ArrayType tv, ArrayType tv)

-- ===================== Binding time analysis ============================

typeInference :: Map.Map ID Scheme -> SPL -> TI TypeEnv
typeInference env e = do tiSPL (TypeEnv env) e

-- typeInference2 :: TypeEnv -> SPL -> TI TypeEnv
-- typeInference2 env e =
--     do  (s, t) <- ti env e
--         return (apply s env)

-- hello :: TypeEnv -> SPL -> ExceptT ID (State TIState) TypeEnv
-- hello env spl = do 
--                             (s1,t1) <- tiSPL env spl
--                             -- (s2,t2) <- ti (apply s1 env) (SPL decls)
--                             -- return (s2 `composeSubst` s1, t1)
--                             return $ apply s1 env

-- test3 :: SPL -> IO ()
-- test3 e =
--     let (res, s) = runTI (hello (TypeEnv Map.empty) e)
--     in case res of
--          Left err  ->  putStrLn $ show e ++ "\nerror: " ++ err
--          Right t   ->  putStrLn $ show e ++ " :: " ++ show t
         
-- main3 :: String -> IO()
-- main3 filename = do
--        file <- readFile $ splFilePath++filename
--        case tokeniseAndParse mainSegments file of 
--               Right (x, _) -> test3 x
--               Left x -> do print x


-- ===================== Tests ============================
test1 :: SPL -> IO ()
test1 e =
    let (res, s) = runTI (typeInference Map.empty e)
    in case res of
         Left err  ->  putStrLn $ show e ++ "\nerror: " ++ err
         Right t   ->  putStrLn $ show e ++ "\n\n" ++ show t




env = 
    [
    ("tuple" :: ID, Scheme [] (IdType "x" Nothing))
    ]

expTest8 =
    let (res, s) = runTI (tiExp (TypeEnv (Map.fromList env))  (ExpTuple (ExpId "tuple" (Field [Second]), ExpId "tuple" (Field [First]) )) )
    in case res of
         Left err ->  putStrLn $ "error: " ++ err
         Right (subst, t) ->  putStrLn $ show subst ++ "\n\n" ++ show t


-- ====== Tests regarding tiStmts ======

-- ("flip" :: ID, Scheme [] (TypeBasic BasicBool)),


env'' = 
    [("tuple" :: ID, Scheme [] (IdType "z" Nothing))
    ]


-- stmtsTest1 :: [Stmt] -> IO()
-- stmtsTest1 stmts = let (res, s) = runTI (tiStmtTest (TypeEnv (Map.fromList env'')) (head stmts) )
--     in case res of
--          Left err ->  putStrLn $ "error: " ++ err
--          Right (subst, t1, t2, env) ->  putStrLn $ show subst 
--             ++ "\n\n" ++ show t1 
--             ++ "\n\n" ++ show t2
--             ++ "\n\n" ++ show env






env' = 
    [
    ("first" :: ID, Scheme [] (IdType "x" Nothing)),
    ("sec" :: ID, Scheme [] (IdType "y" Nothing)),
    ("tuple" :: ID, Scheme [] (IdType "z" Nothing))
    ]



-- stmtsTest2 :: [Stmt] -> IO()
-- stmtsTest2 stmts = let (res, s) = runTI (tiStmtsTest (TypeEnv (Map.fromList env')) stmts )
--     in case res of
--          Left err ->  putStrLn $ "error: " ++ err
--          Right (subst, t, env) ->  putStrLn $ show subst ++ "\n\n" ++ show t ++ "\n\n" ++ show env

-- runStmtsTest :: ([Stmt] -> IO()) -> String -> IO()
-- runStmtsTest test filename = do
--        file <- readFile $ splFilePath++filename
--        case tokeniseAndParse (some stmt) file of 
--               Right (x, _) -> do
--                     print x
--                     putStr "\n\n"
--                     test x

--               Left x -> do print x


-- ====== Tests regarding tiFunDecl ======
fundecl = FunDecl "swap" ["tuple"] Nothing [] [StmtDeclareVar "tuple" (Field [First]) (ExpId "tuple" (Field [First])),StmtDeclareVar "tuple" (Field [Second]) (ExpId "tuple" (Field [Second])),StmtReturn (Just (ExpId "tuple" (Field [])))]
fundecl' = FunDecl "swap" ["tuple"] Nothing [] [StmtDeclareVar "tuple" (Field [First]) (ExpId "tuple" (Field [Second])),StmtDeclareVar "tuple" (Field [Second]) (ExpId "tuple" (Field [First]))]
fundecl'' = FunDecl "swap" ["tuple"] Nothing [VarDeclVar "tmp" (ExpId "tuple" (Field [First]))] [StmtDeclareVar "tuple" (Field [First]) (ExpId "tuple" (Field [Second])),StmtDeclareVar "tuple" (Field [Second]) (ExpId "tmp" (Field []))]

fundecl''' = FunDecl "swap" ["tuple"] Nothing [VarDeclVar "tmp" (ExpId "tuple" (Field [First]))] [StmtDeclareVar "tuple" (Field [First]) (ExpId "tuple" (Field [Second])),StmtDeclareVar "tuple" (Field [Second]) (ExpId "tmp" (Field [])),StmtReturn (Just (ExpId "tuple" (Field [])))]


funDeclTest1 ::  IO()
funDeclTest1 = let (res, s) = runTI (tiFunDeclTest (TypeEnv Map.empty) fundecl )
    in case res of
         Left err ->  putStrLn $ "error: " ++ err
         Right (s1,s2,t,  TypeEnv env) ->
                putStrLn $ "\n\nOutput: \n" ++ show s1 ++ "\n\n" ++ 
                show s2 ++ "\n\n" ++
                show t ++ "\n\n" ++
                show env


splTest1:: SPL -> IO()
splTest1 code = let (res, s) = runTI (tiSPL (TypeEnv Map.empty) code )
    in case res of
         Left err ->  putStrLn $ "error: " ++ err
         Right (TypeEnv env) -> print env

swap (a,b) = (b,a)


main1 :: String -> IO()
main1 filename = do
       file <- readFile $ splFilePath++filename
       case tokeniseAndParse mainSegments file of 
              Right (x, _) -> splTest1 x
              Left x -> do print x

-- main2 :: String -> IO()
-- main2 filename = do
--        file <- readFile $ splFilePath++filename
--        case tokeniseAndParse mainSegments file of 
--               Right (x, _) -> test2 x
--               Left x -> do print x
