module TI where

import Error
import Lexer
import AST
import Parser
import ReturnGraph
import MutRec

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

generalizeFuncs :: TypeEnv -> [IDLoc] -> TI TypeEnv
generalizeFuncs env [] = return env
generalizeFuncs (TypeEnv env) (x:xs) = case Map.lookup x env of
    Just (Scheme [] t,scope) -> let scheme = generalize (TypeEnv env) t in
        generalizeFuncs (TypeEnv $ Map.insert x (scheme,GlobalScope) env) xs
    _ ->
        dictate (ErrorD (getDLoc x) ("Function " ++ pp x ++  " is mutual recursive and should therefore be in the type environment but it is not.")) >>
        return (TypeEnv env)

-- ===================== State ============================
insertOp2TI :: Op2Typed -> TI ()
insertOp2TI (Op2 op (Just t) loc) =
    if containsIDType t
        then confess (Error loc "Trying to insert overloaded op2 functions with polymorphic type")
        else do
            (s, (ops, funcCalls)) <- get
            put (s, (Map.insert (overloadedOpName op t) (Op2 op (Just t) loc) ops, funcCalls))

insertFunCallTI :: FunCall -> TI ()
insertFunCallTI (FunCall (ID locA id locB) args (Just (FunType t t'))) =
     if containsIDType t
        then confess (ErrorD (DLoc locA locB) "Trying to insert overloaded op2 functions with polymorphic type")
        else do
            (s, (ops, funcCalls)) <- get
            let f = Map.insert (overloadedTypeName id t) (FunCall (ID locA id locB)[] (Just $ FunType t t')) funcCalls
            put (s, (ops, f))

-- ===================== Scheme ============================
data Scheme =
    Scheme [IDLoc] SPLType |
    OverScheme [IDLoc] SPLType [Op2Typed] [FunCall]
    deriving (Show, Eq)

data Scope = GlobalScope | LocalScope | ArgScope
    deriving (Show,Eq)

find :: IDLoc -> TypeEnv -> Maybe Scheme
find id (TypeEnv env) = fst <$> Map.lookup id env

generalize :: TypeEnv -> SPLType -> Scheme
generalize env t  = Scheme vars t
  where vars = Set.toList (ftv t Set.\\ ftv env)

generalizeOver :: TypeEnv -> SPLType -> [Op2Typed] -> [FunCall] -> Scheme
generalizeOver env t ops funcs = OverScheme vars t ops funcs
    where vars = Set.toList ((ftv t `Set.union` ftv ops `Set.union` ftv funcs ) Set.\\ ftv env)


instantiate :: Scheme -> TI SPLType
instantiate (Scheme vars t) = do
    nvars <- mapM (const newSPLVar) vars
    let s = Map.fromList (zip vars nvars)
    return $ apply s t

instantiateOver :: Scheme -> TI(SPLType,[Op2Typed],[FunCall])
instantiateOver (OverScheme vars t ops funcs) = do
    nvars <- mapM (const newSPLVar) vars
    let s = Map.fromList (zip vars nvars)
    return (apply s t, apply s ops, apply s funcs)


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
    ftv (OverScheme vars t ops funcs) = (ftv t `Set.union` ftv ops `Set.union` ftv funcs) Set.\\ Set.fromList vars
    apply s (Scheme vars t) = Scheme vars (apply (Prelude.foldr Map.delete s vars) t)
    apply s (OverScheme vars t ops funcs) = OverScheme vars (apply (Prelude.foldr Map.delete s vars) t) ops' funcs'
        where ops' = apply (Prelude.foldr Map.delete s vars) ops
              funcs' = apply (Prelude.foldr Map.delete s vars) funcs

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
        return $ IdType (idLocCreator ('a':show s))
--   where
--     toTyVar :: Int -> String
--     toTyVar c | c < 26    =  [toEnum (97+c)]
--               | otherwise = let (n, r) = c `divMod` 26
--                             in toEnum (97+r) : toTyVar (n-1)

newSPLVarLoc :: Loc -> TI SPLType
newSPLVarLoc loc =
    do  (s,overloaded) <- get
        put (s+1,overloaded)
        return $ IdType (ID loc ('a':show s) loc )
--   where
--     toTyVar :: Int -> String
--     toTyVar c | c < 26    =  [toEnum (97+c)]
--               | otherwise = let (n, r) = c `divMod` 26
--                             in toEnum (97+r) : toTyVar (n-1)

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
                    trace ("No 'poly' overloading in " ++ pp funName) $
                    return (cs2, TI.insert (apply cs2 env) funName finaleScheme GlobalScope, funDecl)
                else
                    confess (Error (getFstLoc funName) ("Some functions require overloaded built-ins (print, ==, <, >, etc) but the type for these functions is unkown.\n" 
                                                ++"It is thus impossible to create these for you."))


            
tiFunDecl env (FunDecl funName args (Just funType) vars stmts) =
    if (not $ isGoodScope GlobalScope funName env)
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

                    let funType' = apply cs2 funType
                    let funDecl = FunDecl funName args (Just funType') (apply cs2 vars') (apply cs2 stmts')

                    (funDecl', overloaded) <- monomorphize funDecl env'''
                    let (polyOp2, polyFunCall) = toListOL overloaded
                    if  nullOL overloaded
                        then
                            trace ("No 'poly' overloading in " ++ pp funName) $
                            -- let funcScheme = trace ("\n\nFree stuff in: " ++pp funName ++ "\n" ++ pp funType ++"\n" ++ pp (Set.toList $ ftv funType) ++ "\n\n" ++ pp (Set.toList $ ftv env)++ "\n\n") generalize env funType in
                            let funcScheme = generalize env funType in
                            return (cs2, TI.insert (apply cs2 env) funName funcScheme GlobalScope, funDecl')
                        else
                            trace ("Poly overloading in " ++ pp funName {-- ++ "\n\n" ++ show polyOp2 ++ "\n\n" ++ show polyFunCall --}) $ do
                                let (args', fType', scheme) = overloadFunction args funType env polyOp2 polyFunCall
                                let FunDecl funName' _ (Just _) vars'' stmts'' = funDecl'
                                return (cs2, TI.insert (apply cs2 env) funName scheme GlobalScope, FunDecl funName' args' (Just fType') vars'' stmts'')
                                -- return (scheme, FunDecl funName' args' (Just fType') vars' stmts')



                    -- return (cs2, TI.insert (apply cs2 env) funName finalScheme GlobalScope, finalFunDecl)

                    -- return (cs2, TI.insert env' funName func GlobalScope, FunDecl funName args (Just funType') vars' stmts')
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

        -- let Just (Scheme [] t) = find funName env'''

        let funType = apply cs2 fType

        -- trace ("HIERZO "++ pp funName ++ "\n" ++ printEnv env''' ++ printSubst (Map.toList cs1) ++  pp funType ++ "\nEND") $ do
        let funDecl = FunDecl funName args (Just funType) (apply cs2 vars') (apply cs2 stmts')
        -- let funDecl = FunDecl funName args (Just funType) vars' stmts'


        (funDecl', overloaded) <- monomorphize funDecl env'''
        let (polyOp2, polyFunCall) = toListOL overloaded
        if  nullOL overloaded
            then
                trace ("No 'poly' overloading in " ++ pp funName) $
                -- let funcScheme = trace ("\n\nFree stuff in: " ++pp funName ++ "\n" ++ pp funType ++"\n" ++ pp (Set.toList $ ftv funType) ++ "\n\n" ++ pp (Set.toList $ ftv env)++ "\n\n") generalize env funType in
                let funcScheme = generalize env funType in
                return (cs2, TI.insert (apply cs2 env) funName funcScheme GlobalScope, funDecl')
            else
                trace ("Poly overloading in " ++ pp funName {-- ++ "\n\n" ++ show polyOp2 ++ "\n\n" ++ show polyFunCall --}) $ do
                    let (args', fType', scheme) = overloadFunction args funType env polyOp2 polyFunCall
                    let FunDecl funName' _ (Just _) vars'' stmts'' = funDecl'
                    return (cs2, TI.insert (apply cs2 env) funName scheme GlobalScope, FunDecl funName' args' (Just fType') vars'' stmts'')




        -- (finalScheme, finalFunDecl) <- overloadFunction2 funDecl env'''

        -- trace ("FINAL ENV " ++ pp funName ++ "\n" ++ printEnv (TI.insert (apply cs2 env) funName finalScheme GlobalScope)) $ return (cs2, TI.insert (apply cs2 env) funName finalScheme GlobalScope, finalFunDecl)


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
    (s1, t, funCall',_) <- tiFunCall env False funCall
    return (s1, Nothing, StmtFuncCall  funCall' loc)

tiStmt env (StmtReturn Nothing (Loc line col)) =
    return (nullSubst, Just (Void (Loc line col) (Loc line (col+6))), StmtReturn Nothing (Loc line col))
tiStmt env (StmtReturn (Just e) loc) = do
    (s1, t1, e') <- tiExp env e
    return (s1, Just t1, StmtReturn (Just e') loc)

tiStmt (TypeEnv env) (StmtAssignVar id (Field []) e typ) =
    case Map.lookup id env of
    Just (Scheme [] t,s)  -> do
        (s1, t1, e') <- tiExp (TypeEnv env) e
        s2 <- mgu (apply s1 t) t1
        let cs1 = s2 `composeSubst` s1
        return (cs1, Nothing, StmtAssignVar id (Field []) e' (Just t1))
    Nothing ->
        dictate (refBeforeDec "Variable:" id) >>
        return (nullSubst, Nothing, StmtAssignVar id (Field []) e typ)
tiStmt (TypeEnv env) (StmtAssignVar id (Field fields) e typ) = case Map.lookup id env of
    Just (Scheme [] t,s)  -> do
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
    s2 <-  injectErrLocMsg nullSubst (mgu (apply cs1 t) t1) (getDLoc e) ("Argument '"++ pp e ++ "' should have type "++ pp t)
    -- s2 <- trace ("Argument '"++ pp e ++ "' should have type "++ pp t ++ " and has "++ pp t1) $  injectErrLoc nullSubst (mgu (apply cs1 t) t1) (getDLoc e)
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
tiExp env (ExpId id (Field [])) = do
    case find id env of
        Just (Scheme [] t) -> return (nullSubst, t, ExpId id (Field []))
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
-- overloadFunction2 (FunDecl funName args (Just funType) vars stmts) env = do




overloadFunction :: [IDLoc] -> SPLType -> TypeEnv ->  [Op2Typed] -> [FunCall] -> ([IDLoc], SPLType, Scheme)
overloadFunction args fType env ops funcs = do
    let (argsOps, ops', typeOps) = combine $ Prelude.map opToStuff ops
    let (argsFuncs, funcs', typeFuncs) = combine $ Prelude.map funcToStuff funcs
    let args' = args ++ argsOps ++ argsFuncs
    -- trace ("overloadFunction\n" ++ show (zip argsFuncs typeFuncs) ++ "\nend overloadFunction") $ do
    let fType' =
                let typesOfArgs = getArgsTypes fType
                in foldr1 FunType (init typesOfArgs ++ typeOps ++ typeFuncs ++ [last typesOfArgs] )
    let scheme = generalizeOver env fType' ops funcs
    (args', fType', scheme)
    where
        combine [] = ([],[],[])
        combine (x:xs) = (\(a,b,c) (as,bs,cs) -> (a:as,b:bs,c:cs) ) x (combine xs)
        opToStuff (Op2 op (Just (FunType t t')) loc) =
            (idLocCreator $ overloadedOpName op t,Op2 op (Just (FunType t t')) loc, FunType t t')
        funcToStuff (FunCall (ID locA "print" locB) args (Just (FunType t t'))) =
            (idLocCreator $ overloadedTypeName "print" t,FunCall (ID locA "print" locB) args (Just (FunType t t')), FunType t t')



overloadedTypeName :: String -> SPLType -> String
overloadedTypeName start t = '_':start ++ typeToName t

overloadedOpName :: Op2 -> SPLType -> String
overloadedOpName op t = '_':op2String op ++ typeToName t

typeToName :: SPLType -> String
typeToName (TypeBasic _ x _) = pp x
typeToName (TupleType _ (t1,t2) _) = "Tuple" ++ typeToName t1 ++ typeToName t2
typeToName (ArrayType _ a1 _) = "Array"++ typeToName a1
typeToName (FunType arg f) = typeToName arg ++"-"++ typeToName f
typeToName (Void _ _) = "Void"
typeToName (IdType id) = pp id

op2String :: Op2 -> String
op2String Le  = "lt"
op2String Ge  = "gt"
op2String Leq = "le"
op2String Geq = "ge"
op2String Eq  = "eq"
op2String Neq = "ne"


data Overloaded = OL (Map String Op2Typed) (Map String FunCall)

instance Show Overloaded where
    show (OL a b) = "OPS:\n" ++ intercalate "\n" (Prelude.map show (Map.elems a)) ++ "\n\nFUNCS:\n" ++ intercalate "\n" (Prelude.map show (Map.elems b))

emptyOL :: Overloaded
emptyOL = OL Map.empty Map.empty

singletonOLOp :: Op2Typed -> Overloaded
singletonOLOp (Op2 op (Just t) loc) = OL (Map.singleton key (Op2 op (Just t) loc)) Map.empty
    where key = overloadedOpName op t

singletonOLFun :: FunCall -> Overloaded
singletonOLFun (FunCall (ID locA id locB) es (Just t)) = OL Map.empty (Map.singleton key (FunCall (ID locA id locB) es (Just t)))
    where key = overloadedTypeName id t

unionOL :: Overloaded -> Overloaded -> Overloaded
unionOL (OL a b) (OL c d) = OL (Map.union a c) (Map.union b d)

toListOL :: Overloaded -> ([Op2Typed], [FunCall])
toListOL (OL a b) = (Map.elems a, Map.elems b)

nullOL :: Overloaded -> Bool
nullOL (OL a b) = Map.null a && Map.null b

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

instance Monomorphization VarDecl where
    monomorphize (VarDeclType t id e) env = do
        (e', ol1) <- monomorphize e env
        return (VarDeclType t id e', ol1)

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
-- findReplaceOLFunCall :: FunCall -> TI (FunCall, [(Op2Typed,IDLoc,SPLType)], [(FunCall, IDLoc, SPLType)])
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
    monomorphize (FunCall id args t) env = return (FunCall id args t, emptyOL)

instance Monomorphization Op2Typed where
    monomorphize (Op2 op (Just (FunType t t')) loc) env | containsIDType (FunType t t') = do
        let name = idLocCreator $ overloadedOpName op t
        return (Op2 op (Just (FunType t t')) loc, singletonOLOp (Op2 op (Just (FunType t t')) loc))
    monomorphize x env = return (x, emptyOL)



-- combineOverFuncs x y = do
--     (a,b) <- x
--     (c,d) <- y
--     return (a++c,b++d)

containsIDTypeMaybe :: Maybe SPLType -> Bool
containsIDTypeMaybe Nothing = False
containsIDTypeMaybe (Just t) = containsIDType t

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
printEnv :: TypeEnv -> String
printEnv (TypeEnv env) = printEnv1 (Map.toList env)

printEnv1 :: [(IDLoc, (Scheme,Scope))] -> String
printEnv1 [] = ""
printEnv1 ((ID _ id _,(Scheme v t,GlobalScope)):xs) = id ++" :: " ++ pp t ++", "++ pp v ++ " Global\n"++ printEnv1 xs
printEnv1 ((ID _ id _,(Scheme v t,LocalScope)):xs) = id ++" :: " ++ pp t ++", "++ pp v ++ " Local\n"++ printEnv1 xs
printEnv1 ((ID _ id _,(Scheme v t,ArgScope)):xs) = id ++" :: " ++ pp t ++", "++ pp v ++ " arg\n"++ printEnv1 xs
printEnv1 ((ID _ id _,(OverScheme v t _ _,LocalScope)):xs) = id ++" :: " ++ pp t ++", "++ pp v ++ " over Local\n"++ printEnv1 xs
printEnv1 ((ID _ id _,(OverScheme v t _ _,GlobalScope)):xs) = id ++" :: " ++ pp t ++", "++ pp v ++ " over Global\n"++ printEnv1 xs
printEnv1 ((ID _ id _,(OverScheme v t _ _,ArgScope)):xs) = id ++" :: " ++ pp t ++ ", "++ pp v ++ " over arg\n"++ printEnv1 xs


printSubst :: [(IDLoc,SPLType)] -> String
printSubst [] = ""
printSubst ((ID _ id _,t):xs) = id ++ " -> " ++ pp t ++ "\n"++ printSubst xs

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
    apply s (ExpOp2 locA e1 op e2 locB) = do
        let e1' = apply s e1
        let e2' = apply s e2
        let op' = apply s op
        ExpOp2 locA e1' op'  e2' locB
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

instance Types Op2Typed where
    apply s (Op2 op (Just t) loc) = Op2 op (Just (apply s t)) loc
    apply s x = x
    ftv (Op2 op (Just t) loc) = ftv t
    ftv _ = undefined

instance Types FunCall where
    apply s (FunCall (ID locA name locB) es (Just t)) = do
        let es' = apply s es
        FunCall (ID locA name locB) es' (Just $ apply s t)
    apply s (FunCall id es Nothing) = FunCall id es Nothing
    ftv (FunCall (ID locA name locB) es (Just t)) = ftv t
    ftv _ = undefined



mainTIIO filename = do
    -- path <- getCurrentDirectory
    -- print path
    file <- readFile  ("../SPL_test_code/" ++ filename)
    case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= typeInference of
        Right (s1, env, code) -> do
            putStr $ pp code
            putStr $ "\nEnv:\n" ++ printEnv env
            putStr $ "\nSubst:\n" ++ printSubst (Map.toList s1)
        Left x -> putStr $ showError file x


eq = FunDecl (ID (Loc 6 1) "equal" (Loc 6 6)) [ID (Loc 6 7) "x" (Loc 6 8),ID (Loc 6 10) "y" (Loc 6 11)] Nothing [] [StmtReturn (Just (ExpOp2 (Loc 7 14) (ExpId (ID (Loc 7 12) "x" (Loc 7 13)) (Field [])) (Op2 Eq Nothing (Loc 7 14)) (ExpId (ID (Loc 7 17) "y" (Loc 7 18)) (Field [])) (Loc 7 16))) (Loc 7 5)]

tiObject = do
    -- path <- getCurrentDirectory
    -- print path
    case runTI (tiFunDecl (TypeEnv Map.empty) eq) of
        (That (s1, env, code),_) -> do
            print code
            putStr "\n\n"
            putStr $ pp code
            putStr $ "\nEnv:\n" ++ printEnv env
            putStr $ "\nSubst:\n" ++ printSubst (Map.toList s1)
        (This x,_) -> print x
        (These x _,_) -> print x


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

