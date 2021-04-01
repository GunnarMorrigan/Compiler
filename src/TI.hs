module BTA where

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

instance Types a => Types [a] where
    ftv l = Prelude.foldr (Set.union . ftv) Set.empty l
    apply s = Prelude.map (apply s)

-- ===================== Substitution ============================
type Subst = Map.Map ID AllType

nullSubst :: Subst
nullSubst = Map.empty 

composeSubst::Subst -> Subst -> Subst 
composeSubst s1 s2 = Map.map (apply s1) s2 `Map.union` s1

-- ===================== Type inference ============================

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

-- TODO Change TI stuff to Either
class MGU a where
    mgu :: a -> a -> TI Subst

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

instance MGU a => MGU [a] where
    mgu [] [] = return nullSubst
    mgu (x:xs) (y:ys) = do s1 <- mgu x y
                           s2 <- mgu xs ys
                           return (s1 `composeSubst` s2) 


class GetParamType a where
    getParamType :: TypeEnv -> ID -> a -> TI (Subst, AllType)

instance GetParamType Stmt where
    getParamType env id (StmtIf exp stmts Nothing) = undefined
    getParamType env id (StmtIf exp stmts (Just elseStmts)) = undefined 

instance GetParamType Exp where
    getParamType env id (ExpId id' (Field fields)) | id == id' = do
        return undefined 

getType :: TypeEnv -> AllType -> [StandardFunction] -> TI (Subst, AllType)
getType env t [x] = do
    tv <- fieldType x
    let AFunType (FunType [idtype] (RetSplType retType)) = tv
    s1 <- mgu t (ASPLType idtype)
    return (s1, ASPLType idtype)
getType env t (x:xs) = do
    tv <- fieldType x
    let AFunType (FunType [idtype] (RetSplType retType)) = tv
    s1 <- mgu t (ASPLType idtype)
    (s2,t2) <- getType (apply s1 env) t xs
    let cs1 = s2 `composeSubst` s1
    
    return undefined


varBind :: ID -> AllType -> TI Subst
varBind id (ASPLType (IdType t)) | id == t  = return nullSubst
varBind id t | id `Set.member` ftv t = throwError $ "occurs check fails: " ++ id ++ " vs. " ++ show t
varBind id t = return (Map.singleton id t)

tiSPL :: TypeEnv -> SPL -> TI TypeEnv
tiSPL env (SPL [decl]) = do tiDecl env decl
tiSPL env (SPL (decl:decls)) = do 
            env' <- tiDecl env decl
            tiSPL env' (SPL decls)

tiDecl :: TypeEnv -> Decl -> TI TypeEnv
tiDecl env (VarMain x) = tiVarDecl env x
tiDecl env (FuncMain x) = tiFunDecl env x

tiVarDecl :: TypeEnv -> VarDecl -> TI TypeEnv
tiVarDecl (TypeEnv env) (VarDeclVar id e) = do
    --tv <- newASPLVar
    (s1, t1) <- tiExp (TypeEnv env) e
    let t' = generalize (apply s1 (TypeEnv env)) t1
    let env' = TypeEnv (Map.insert id t' env)
    -- s2 <- mgu (apply s1 t1) (ASPLType $ IdType id)
    return env'
tiVarDecl (TypeEnv env) (VarDeclType t id e) = do
    (s1, t1) <- tiExp (TypeEnv env) e
    s2 <- mgu (apply s1 (ASPLType t)) t1
    let t' = generalize (apply (s2 `composeSubst` s1) (TypeEnv env)) t1
    let env' = TypeEnv (Map.insert id t' env)
    return env'

tiFunDecl :: TypeEnv -> FunDecl -> TI TypeEnv
tiFunDecl env (FunDecl funName params (Just funType) vars stmts) = undefined  
tiFunDecl env (FunDecl funName params Nothing vars stmts) = do
    retType <- newSPLVar
    (s1,t1) <- getReturnType env stmts
    s1 <- mgu (apply s1 $ ARetType $ RetSplType retType) t1
    return undefined 

getReturnType :: TypeEnv -> [Stmt]-> TI (Subst, AllType)
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
        Nothing -> throwError $ "id: '" ++ id ++ "', does not exist in the type environment"
tiExp env (ExpId id field) = undefined
tiExp _ (ExpInt i) = return (nullSubst, ASPLType (TypeBasic BasicInt))
tiExp _ (ExpBool b) = return (nullSubst, ASPLType (TypeBasic BasicBool))
tiExp _ (ExpChar c) = return (nullSubst, ASPLType (TypeBasic BasicChar))
tiExp env (ExpBracket e) = tiExp env e
tiExp env x | x == ExpList [] || x == ExpEmptyList = do 
      tv <- newASPLVar
      return (nullSubst, tv)
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
tiExp env (ExpOp1 e op) = undefined

fieldType :: StandardFunction -> TI AllType
fieldType Head = do 
    tv <- newSPLVar
    return $ AFunType $ FunType [ArrayType tv] (RetSplType tv)
fieldType Tail = do
    tv <- newSPLVar
    return $ AFunType $ FunType [ArrayType tv] (RetSplType $ ArrayType tv)
fieldType First = do
    a <- newSPLVar
    b <- newSPLVar
    return $ AFunType $ FunType [TupleType (a, b)] (RetSplType a)
fieldType Second = do
    a <- newSPLVar
    b <- newSPLVar
    return $ AFunType $ FunType [TupleType (a, b)] (RetSplType b)
fieldType IsEmpty = do
    tv <- newSPLVar
    return $ AFunType $ FunType [ArrayType tv] (RetSplType $ TypeBasic BasicBool)

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


test1 :: SPL -> IO ()
test1 e =
    let (res, s) = runTI (typeInference Map.empty e)
    in case res of
         Left err  ->  putStrLn $ show e ++ "\nerror: " ++ err
         Right t   ->  putStrLn $ show e ++ " :: " ++ show t

-- test2 :: SPL -> IO ()
-- test2 e =
--     let (res, s) = runTI (ti (TypeEnv Map.empty) e)
--     in case res of
--          Left err  ->  putStrLn $ show e ++ "\nerror: " ++ err
--          Right t   ->  putStrLn $ show e ++ " :: " ++ show t

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












-- type Context = Map.Map ID AllType 

-- -- freshVariable :: Int -> String
-- freshVariable x = ASPLType $ IdType $ 'a':show x



-- test = tokeniseAndParse mainSegments "var hoi = 10;\n var hoi = 11;\n var a = 'a';"
-- -- funcTest test = 

-- main2 :: String -> IO()
-- main2 filename = do
--        file <- readFile $ splFilePath++filename
--        case tokeniseAndParse mainSegments file of 
--               Right (x, _) -> do print $ show $ bta x 0 Map.empty
--               Left x -> do print x



-- class BTA a where
--     bta :: a -> Int -> Context -> Either Error Context

-- -- instance BTA (Either Error (SPL, [(Token, Int, Int)])) where
-- --     bta (Right (x,_)) = bta x 0 Map.empty 
-- --     bta (Left error) = Left error




-- instance BTA SPL where
--     bta (SPL x) _ _ = bta x 0 Map.empty

-- instance BTA a => BTA [a] where
--     bta [] _ c = Right c
--     bta (x:xs) freshCount c = do
--         first <- bta x freshCount c
--         second <- bta xs freshCount first
--         Right $ first `Map.union` second

-- instance BTA Decl where
--     bta (VarMain x) c = bta x c
--     bta (FuncMain x) c = undefined --bta x c

-- instance BTA VarDecl where
--     bta (VarDeclVar id exp) f c = if Map.member id c then Left (Error 0 0 "duplicate var decl") else Right (Map.insert id (freshVariable f) c)
--     bta (VarDeclType t id exp) f c = undefined --Right $ Map.singleton id (ASPLType t)




-- -- instance BTA FunDecl where
-- --     bta (FunDecl funName args funType vars stmt) = 
