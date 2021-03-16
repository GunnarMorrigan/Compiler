module BTA where

import Parser
import AST
import Lexer

import Data.Map as Map
import Data.Set as Set

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State

-- ===================== TypeEnv ============================
newtype TypeEnv = TypeEnv (Map ID AllType)

remove :: TypeEnv -> ID -> TypeEnv
remove (TypeEnv id) = undefined 

generalize :: TypeEnv -> AllType -> Scheme
generalize env t  =   Scheme vars t
  where vars = Set.toList (ftv t Set.\\ ftv env)

instance Types TypeEnv where
    ftv (TypeEnv env)      =  ftv (Map.elems env)
    apply s (TypeEnv env)  =  TypeEnv (Map.map (apply s) env)

-- ===================== AllType ============================
data AllType = ASPLType SPLType  
             | AFunType FunType
             | PolyType
             deriving (Eq)
instance Show AllType where
    show (ASPLType x) = show x 
    show (AFunType x) = show x
    show PolyType = "POLY?" 
    
-- ===================== Scheme ============================
data Scheme = Scheme [ID] AllType
    deriving (Show, Eq)

instance Types Scheme where
    ftv (Scheme vars t) = ftv t Set.\\ Set.fromList vars
    apply s (Scheme vars t) = Scheme vars (apply (Prelude.foldr Map.delete s vars) t)

class Types a where
    ftv :: a -> Set ID 
    apply :: Subst -> a -> a

instance Types AllType where
    ftv (ASPLType x) = ftv x
    ftv (AFunType x) = ftv x
    ftv PolyType = Set.empty
    apply s (ASPLType x) = ASPLType (apply s x)
    apply s (AFunType x) = AFunType (apply s x)
    
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
    apply s (ArrayType x) = apply s x
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
    apply s = Prelude.map (apply s)
    ftv l = Prelude.foldr (Set.union . ftv) Set.empty l

-- ===================== Substitution ============================
type Subst = Map.Map ID AllType

nullSubst :: Subst
nullSubst = Map.empty 

composeSubst::Subst -> Subst -> Subst 
composeSubst s1 s2 = Map.map (apply s1) s2 `Map.union` s1

-- ===================== Type inference ============================

data TIEnv = TIEnv  {}
type TIState = Int
type TI a = ExceptT ID (State TIState) a

runTI :: TI a -> (Either ID a, TIState)
runTI t = runState (runExceptT t) initTIState
  where initTIState = 0

newVar :: TI AllType 
newVar =
    do  s <- get
        put (s + 1)
        return (ASPLType (IdType (reverse (toTyVar s))))
  where 
    toTyVar :: Int -> String
    toTyVar c | c < 26    = [toEnum (97+c)]
              | otherwise = let (n, r) = c `divMod` 26
                            in toEnum (97+r) : toTyVar (n-1)


instantiate :: Scheme -> TI AllType
instantiate (Scheme vars t) = do  nvars <- mapM (const newVar) vars
                                  let s = Map.fromList (zip vars nvars)
                                  return $ apply s t

-- TODO Change TI stuff to Either
class MGU a where
    mgu :: a -> a -> TI Subst

instance MGU AllType where
    mgu (AFunType l) (AFunType r) = do mgu l r
    mgu (ASPLType l) (ASPLType r) = do mgu l r
    mgu t1 t2 =  throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

-- mgu (TFun l r) (TFun l' r')  =  do  s1 <- mgu l l'
--                                     s2 <- mgu (apply s1 r) (apply s1 r')
--                                     return (s1 `composeSubst` s2)
instance MGU FunType where
    mgu (FunType xs retx) (FunType ys rety) = do s1 <- mgu xs ys
                                                 s2 <- mgu (apply s1 retx) (apply s1 rety)  
                                                 return (s1 `composeSubst` s2)

instance MGU SPLType where
    mgu (TupleType (l1,r1)) (TupleType (l2,r2)) = do s1 <- mgu l1 l2
                                                     s2 <- mgu r1 r2
                                                     return (s1 `composeSubst` s2)     
    mgu (ArrayType x) (ArrayType y) = do mgu x y
    mgu (IdType l) r = do varBind l r
    mgu l (IdType r) = do varBind r l
    mgu t1 t2 =  throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

instance MGU BasicType where
    mgu a b | a == b = return nullSubst
    mgu t1 t2 =  throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

instance MGU RetType where
    mgu Void Void = return nullSubst  
    mgu (RetSplType x) (RetSplType y) = do mgu x y
    mgu t1 t2 =  throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

instance MGU a => MGU [a] where
    mgu [] [] = return nullSubst
    mgu (x:xs) (y:ys) = do s1 <- mgu x y
                           s2 <- mgu xs ys
                           return (s1 `composeSubst` s2) 

varBind :: ID -> SPLType -> TI Subst
varBind id t | t == IdType id = return nullSubst
             | id `Set.member` ftv t = throwError $ "occurs check fails: " ++ id ++ " vs. " ++ show t
             | otherwise = return (Map.singleton id (ASPLType t))

-- mgu (TVar u) t               =  varBind u t
-- mgu t (TVar u)               =  varBind u t
-- mgu TInt TInt                =  return nullSubst
-- mgu TBool TBool              =  return nullSubst
-- mgu t1 t2                    =  throwError $ "types do not unify: " ++ show t1 ++
--                                 " vs. " ++ show t2




-- function :: SPL -> TypeEnv -> Either Error (a, [(Token, Int, Int)])
-- function (SPL ((VarMain v):xs)) env = undefined 
-- function (SPL ((FuncMain f):xs)) env = undefined

-- varDeclBTA v decls

-- varDeclBTA :: VarDecl -> Declarations  -> Either Error (a, [(Token, Int, Int)])
-- varDeclBTA (VarDeclVar id exp) decls = undefined
-- varDeclBTA (VarDeclType spltype id exp) decls = undefined

-- checkExpr :: Declarations ->


-- ===================== Binding time analysis ============================
type Context = Map.Map ID AllType 

class BTA a where
    bta :: a -> Either Error Context

instance BTA SPL where
    bta (SPL ((VarMain x):xs)) = bta x 

instance BTA VarDecl where
    bta (VarDeclVar id exp) = undefined
    bta (VarDeclType t id exp) = Right $ Map.singleton id (ASPLType t)