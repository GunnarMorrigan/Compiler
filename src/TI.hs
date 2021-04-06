module TI where

import Parser
import AST
import Lexer

import Data.Map as Map
import Data.Set as Set

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import System.Exit
import System.Directory

-- ===================== TypeEnv ============================
newtype TypeEnv = TypeEnv (Map ID Scheme)
    deriving (Show)

remove :: TypeEnv -> ID -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

find :: ID -> TypeEnv -> Maybe AllType
find id (TypeEnv env) = do 
    (Scheme _ t) <- Map.lookup id env
    return t

generalize :: TypeEnv -> AllType -> Scheme
generalize env t  =   Scheme vars t
  where vars = Set.toList (ftv t Set.\\ ftv env)

-- ===================== AllType ============================
data AllType = ASPLType SPLType  
             | AFunType FunType
             | ARetType RetType
             deriving (Eq, Show)
instance PrettyPrinter AllType where
    pp (ASPLType x) = pp x 
    pp (AFunType x) = pp x
    pp (ARetType x) = pp x
    
-- ===================== Scheme ============================
data Scheme = Scheme [ID] AllType
    deriving (Show, Eq)

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

instance Types AllType where
    ftv (ASPLType x) = ftv x
    ftv (AFunType x) = ftv x
    ftv (ARetType x) = ftv x
    -- ftv PolyType = Set.empty
    apply s (ASPLType x) = ASPLType (apply s x)
    apply s (AFunType x) = AFunType (apply s x)
    apply s (ARetType x) = ARetType (apply s x)
    
instance Types SPLType where
    ftv (TypeBasic x) = Set.empty
    ftv (TupleType (x,y)) = ftv x `Set.union` ftv y
    ftv (ArrayType x) = ftv x
    ftv (IdType x) = Set.singleton x
    apply s (IdType x) = case Map.lookup x s of
                        Just (ASPLType t) -> t
                        Just (AFunType t) -> IdType x
                        Nothing -> IdType x
    apply s (TupleType (x,y)) = TupleType (apply s x, apply s y)
    apply s (ArrayType x) = ArrayType (apply s x)
    apply _ x = x

instance Types FunType where
    ftv (FunType args ret) = ftv args `Set.union` ftv ret
    apply s (FunType x r) = FunType (apply s x) (apply s r)

instance Types RetType where
    ftv Void = Set.empty
    ftv (RetSplType x) = ftv x
    apply s (RetSplType st) = RetSplType (apply s st)
    apply _ Void = Void

-- ===================== Substitution ============================
type Subst = Map.Map ID AllType

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


newASPLVar :: TI AllType
newASPLVar =
    do  s <- get
        put (s + 1)
        return $ ASPLType (IdType (reverse (toTyVar s)))
  where 
    toTyVar :: Int -> String
    toTyVar c | c < 26    =  [toEnum (97+c)]
              | otherwise = let (n, r) = c `divMod` 26
                            in toEnum (97+r) : toTyVar (n-1)

newSPLVar :: TI SPLType
newSPLVar =
    do  s <- get
        put (s + 1)
        return $ IdType (reverse (toTyVar s))
  where 
    toTyVar :: Int -> String
    toTyVar c | c < 26    =  [toEnum (97+c)]
              | otherwise = let (n, r) = c `divMod` 26
                            in toEnum (97+r) : toTyVar (n-1)

instantiate :: Scheme -> TI AllType
instantiate (Scheme vars t) = do  nvars <- mapM (const newASPLVar) vars
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

instance MGU AllType where
    mgu (AFunType l) (AFunType r) = do mgu l r
    mgu (ASPLType l) (ASPLType r) = do mgu l r
    mgu (ARetType l) (ARetType r) = do mgu l r
    mgu t1 t2 =  throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

instance MGU FunType where
    mgu (FunType xs retx) (FunType ys rety) = do s1 <- mgu xs ys
                                                 s2 <- mgu (apply s1 retx) (apply s1 rety)  
                                                 return (s1 `composeSubst` s2)

instance MGU SPLType where
    mgu (TupleType (l1,r1)) (TupleType (l2,r2)) = do s1 <- mgu l1 l2
                                                     s2 <- mgu r1 r2
                                                     return (s1 `composeSubst` s2)     
    mgu (ArrayType x) (ArrayType y) = do mgu x y
    mgu (TypeBasic x) (TypeBasic y) = do mgu x y
    mgu (IdType l) r = do varBind l (ASPLType r)
    mgu l (IdType r) = do varBind r (ASPLType l)
    mgu t1 t2 =  throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

instance MGU BasicType where
    mgu a b | a == b = return nullSubst
    mgu t1 t2 =  throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

instance MGU RetType where
    mgu Void Void = return nullSubst
    mgu Void (RetSplType (IdType id)) = do varBind id (ARetType Void)
    mgu (RetSplType (IdType id)) Void = do varBind id (ARetType Void)
    mgu (RetSplType x) (RetSplType y) = do mgu x y
    mgu t1 t2 =  throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

varBind :: ID -> AllType -> TI Subst
varBind id (ASPLType (IdType t)) | id == t  = return nullSubst
varBind id t | id `Set.member` ftv t = throwError $ "occurs check fails: " ++ id ++ " vs. " ++ show t
varBind id t = return (Map.singleton id t)

-- ===================== getParamType ============================
-- Meaning the type of a parameter used through out a function.
-- Not sure if this is needed maybe we could just add the parameters at the start to the env and then check as we go.
-- This will also be more efficient, as we dont go through all statements for each param but for all params through each statements at once.


class GetParamType a where
    getParamType :: TypeEnv -> ID -> a -> TI (Subst, AllType)

instance GetParamType Stmt where
    getParamType env id (StmtIf exp stmts Nothing) = undefined
    getParamType env id (StmtIf exp stmts (Just elseStmts)) = undefined 

instance GetParamType Exp where
    getParamType env id (ExpId id' (Field fields)) | id == id' = do
        tv <- newASPLVar
        (s1, t, ret) <- getType tv fields
        return (s1, t)

-- ===================== Type inference ============================

tiSPL :: TypeEnv -> SPL -> TI TypeEnv
tiSPL env (SPL [decl]) = do tiDecl env decl
tiSPL env (SPL (decl:decls)) = do 
            env' <- tiDecl env decl
            tiSPL env' (SPL decls)

tiDecl :: TypeEnv -> Decl -> TI TypeEnv
tiDecl env (VarMain x) = tiVarDecl env x
tiDecl env (FuncMain x) = tiFunDecl env x
-- TODO
tiDecl env (MutRec []) = undefined 
tiDecl env (MutRec (x:xs)) = undefined 

tiVarDecl :: TypeEnv -> VarDecl -> TI  TypeEnv
tiVarDecl (TypeEnv env) (VarDeclVar id e) = case Map.lookup id env of
    Just x -> throwError $ "Variable with name: '" ++ id ++ "', already exist in the type environment: (i.e. double decleration)"
    Nothing -> do
        --tv <- newASPLVar
        (s1, t1) <- tiExp (TypeEnv env) e
        -- let t' = generalize (apply s1 (TypeEnv env)) t1
        let t' = Scheme [] t1
        let env' = TypeEnv (Map.insert id t' env)
        -- s2 <- mgu (apply s1 t1) (ASPLType $ IdType id)
        return $ apply s1 env'
tiVarDecl (TypeEnv env) (VarDeclType t id e) = case Map.lookup id env of
    Just x -> throwError $ "Variable with name: '" ++ id ++ "', already exist in the type environment: (i.e. double decleration)"
    Nothing -> do
        (s1, t1) <- tiExp (TypeEnv env) e
        s2 <- mgu (apply s1 (ASPLType t)) t1
        let cs1 = s2 `composeSubst` s1
        --let t' = generalize (apply cs1 (TypeEnv env)) t1
        let t' = Scheme [] t1
        let env' = TypeEnv (Map.insert id t' env)
        return $ apply cs1 env'

tiFunDecl :: TypeEnv -> FunDecl -> TI TypeEnv
tiFunDecl env (FunDecl funName params (Just funType) vars stmts) = undefined  
tiFunDecl env (FunDecl funName params Nothing vars stmts) = do
    retType <- newSPLVar
    (s1,t1) <- getReturnType env stmts
    s1 <- mgu (apply s1 $ ARetType $ RetSplType retType) t1
    return undefined

getReturnType :: TypeEnv -> [Stmt] -> TI (Subst, AllType)
getReturnType env ((StmtReturn (Just e)):xs) = do 
    (s1, t1) <- tiExp env e
    (s2, t2) <- getReturnType (apply s1 env) xs
    let cs1 = s2 `composeSubst` s1
    s3 <- mgu (apply cs1 t1) (apply cs1 t2)
    let cs2 = s3 `composeSubst` cs1
    return (cs2, apply cs2 t1)
getReturnType env ((StmtReturn Nothing):xs) = do 
    (s1, t1) <- getReturnType env xs
    s2 <- mgu (ARetType Void) t1
    let cs2 = s2 `composeSubst` s1
    return (cs2, ARetType Void)
getReturnType env [] = return (nullSubst, ARetType Void)
getReturnType env (x:xs) = getReturnType env xs

tiExp :: TypeEnv -> Exp -> TI (Subst, AllType)    
tiExp env (ExpId id (Field [])) = do
    case find id env of
        Just t -> return (nullSubst, t)
        Nothing -> throwError $ "id: '" ++ id ++ "', does not exist in the type environment: (i.e. reference before decleration)"
tiExp (TypeEnv env) (ExpId id (Field fields)) = case Map.lookup id env of
    Just (Scheme ids t) -> do 
        (s1, t', ret) <- getType t fields
        return (s1,t')
    Nothing -> throwError $ "id: '" ++ id ++ "', does not exist in the type environment: (i.e. reference before decleration)"
    -- Nothing -> do
    --     t <- newASPLVar
    --     (s1, t', ret) <- getType t fields
    --     return (s1, t') 
tiExp _ (ExpInt i) = return (nullSubst, ASPLType (TypeBasic BasicInt))
tiExp _ (ExpBool b) = return (nullSubst, ASPLType (TypeBasic BasicBool))
tiExp _ (ExpChar c) = return (nullSubst, ASPLType (TypeBasic BasicChar))
tiExp env (ExpBracket e) = tiExp env e
tiExp env x | x == ExpList [] || x == ExpEmptyList = do 
      tv <- newSPLVar
      return (nullSubst, ASPLType $ ArrayType tv)
tiExp env (ExpList (x:xs)) = do
      (s1, t1) <- tiExp env x
      (s2, t2) <- tiExp (apply s1 env) (ExpList xs)
      return (s2 `composeSubst` s1, t2)
tiExp env (ExpOp2 e1 op e2) = do
    tv <- op2Type op
    let AFunType (FunType (t1:t2:_) (RetSplType t3)) = tv
    (s1, t1') <- tiExp env e1
    s2 <- mgu t1' (apply s1 (ASPLType t1))
    let cs1 = s1 `composeSubst` s2
    (s3,t2') <- tiExp (apply cs1 env) e2
    let cs2 = s3 `composeSubst` cs1
    s4 <- mgu (apply cs2 t2') (apply cs2 (ASPLType t2))
    let cs3 = s4 `composeSubst` cs2 
    return (cs3, apply cs3 (ASPLType t3))
tiExp env (ExpOp1 op e) = case op of
    Neg -> do 
        (s1, t1) <- tiExp env e
        s2 <- mgu t1 (ASPLType $ TypeBasic BasicInt)
        return (s2 `composeSubst` s1, t1)
    Not -> do 
        (s1, t1) <- tiExp env e
        s2 <- mgu t1 (ASPLType $ TypeBasic BasicBool)
        return (s2 `composeSubst` s1, t1)


getType :: AllType -> [StandardFunction] -> TI (Subst, AllType, AllType)
getType t [Head] = do
    tv <- newSPLVar
    let t' = ArrayType tv
    let retType = RetSplType tv
    s1 <- mgu t (ASPLType t')
    return (s1, apply s1 (ASPLType t'), ARetType retType)
getType t [Tail] = do
    tv <- newSPLVar
    let t' = ArrayType tv
    let retType = RetSplType $ ArrayType tv
    s1 <- mgu t (ASPLType t')
    return (s1, apply s1 (ASPLType t'), ARetType retType)
getType t [First] = do
    a <- newSPLVar
    b <- newSPLVar
    let t' = TupleType (a, b)
    let retType = RetSplType  a
    s1 <- mgu t (ASPLType t')
    return (s1, apply s1 (ASPLType t'), ARetType retType)
getType t [Second] = do
    a <- newSPLVar
    b <- newSPLVar
    let t' = TupleType (a, b)
    let retType = RetSplType b
    s1 <- mgu t (ASPLType t')
    return (s1, apply s1 (ASPLType t'), ARetType retType)
getType t [IsEmpty] = do
    tv <- newSPLVar
    let t' = ArrayType tv
    let retType = RetSplType $ TypeBasic BasicBool
    s1 <- mgu t (ASPLType t')
    return (s1, apply s1 (ASPLType t'), ARetType retType)
getType t (x:xs) = do
    (s1, t', ret) <- getType t [x]
    let ARetType (RetSplType retType) = ret
    (s2, t'', ret') <- getType (ASPLType retType) xs
    let cs1 = s2 `composeSubst` s1
    let s3 = applySubst s2 s1
    return (s3, apply cs1 t, ret')




op2Type :: Op2 -> TI AllType
op2Type x | x == Plus || x == Min || x == Mult || x == Div || x == Mod = 
    return $ AFunType $ FunType [TypeBasic BasicInt, TypeBasic BasicInt] (RetSplType $ TypeBasic BasicInt)
op2Type x | x == Eq || x == Le || x == Ge || x == Leq || x == Geq || x == Neq = do
    tv <- newSPLVar
    return $ AFunType $ FunType [tv, tv] (RetSplType $ TypeBasic BasicBool)
op2Type x | x== And || x == Or = 
    return $ AFunType $ FunType [TypeBasic BasicBool, TypeBasic BasicBool] (RetSplType $ TypeBasic BasicBool)
op2Type Con = do 
    tv <- newSPLVar
    return $ AFunType $ FunType [tv , ArrayType tv] (RetSplType $ ArrayType tv)

-- ===================== Binding time analysis ============================

help :: TypeEnv
help = TypeEnv Map.empty 

typeInference :: Map.Map ID Scheme -> SPL -> TI TypeEnv
typeInference env e =
    do tiSPL (TypeEnv env) e

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

-- ====== Tests regarding tiExp ======
test2 :: IO ()
test2 =
    let (res, s) = runTI (getType (ASPLType $ IdType "hoi") [Head, Second, Head] )
    in case res of
         Left err  ->  putStrLn $ "error: " ++ err
         Right (subst, t, ret)   ->  putStrLn $ show subst ++ "\n\n" ++ show t ++ "\n\n" ++ show ret

test3 :: IO ()
test3 =
    let (res, s) = runTI (tiExp (TypeEnv Map.empty) (ExpId "hoi" (Field [Head, Second, Head])))
    in case res of
         Left err  ->  putStrLn $ "error: " ++ err
         Right (subst, t)   ->  putStrLn $ show subst ++ "\n\n" ++ show t

test4 :: IO ()
test4 =
    let (res, s) = runTI (tiExp (TypeEnv (Map.fromList [("hoi" :: ID, Scheme [] (ASPLType (ArrayType (TupleType (IdType "z",ArrayType (IdType "x"))))) )] )) (ExpId "hoi" (Field [Head, Second, Head])))
    in case res of
         Left err  ->  putStrLn $ "error: " ++ err
         Right (subst, t)   ->  putStrLn $ show subst ++ "\n\n" ++ show t

test5 :: IO ()
test5 =
    let (res, s) = runTI (tiExp (TypeEnv Map.empty) ExpEmptyList)
    in case res of
         Left err  ->  putStrLn $ "error: " ++ err
         Right (subst, t)   ->  putStrLn $ show subst ++ "\n\n" ++ show t

test6 =
    let (res, s) = runTI (tiExp (TypeEnv Map.empty) (ExpOp1 Neg $ ExpInt 10))
    in case res of
         Left err ->  putStrLn $ "error: " ++ err
         Right (subst, t) ->  putStrLn $ show subst ++ "\n\n" ++ show t

test7 =
    let (res, s) = runTI (tiExp (TypeEnv (Map.fromList [("hoi" :: ID, Scheme [] (ASPLType $ TypeBasic BasicBool) )])) (ExpOp1 Not $ ExpId "hoi" (Field [])))
    in case res of
         Left err ->  putStrLn $ "error: " ++ err
         Right (subst, t) ->  putStrLn $ show subst ++ "\n\n" ++ show t

main1 :: String -> IO()
main1 filename = do
       file <- readFile $ splFilePath++filename
       case tokeniseAndParse mainSegments file of 
              Right (x, _) -> test1 x
              Left x -> do print x

-- main2 :: String -> IO()
-- main2 filename = do
--        file <- readFile $ splFilePath++filename
--        case tokeniseAndParse mainSegments file of 
--               Right (x, _) -> test2 x
--               Left x -> do print x
