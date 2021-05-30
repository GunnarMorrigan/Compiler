module TImisc where

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
    deriving (Eq, Show)

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
instantiate (OverScheme vars t ops funcs) = do
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

instance Types a =>  Types (Maybe a) where
    ftv (Just a) = ftv a
    ftv Nothing = Set.empty
    apply s (Just a) = Just $ apply s a
    apply s Nothing = Nothing

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
    apply s (VarDeclType t id e) = VarDeclType (apply s t) id (apply s e)
    apply s e = e
    ftv = undefined

instance Types FunDecl where
    apply s (FunDecl funName args funType varDecls stmts) = do
        let varDecls' = apply s varDecls
        let stmts' = apply s stmts
        FunDecl funName args (apply s funType) varDecls' stmts'
    ftv = undefined

instance Types Stmt where
    -- apply s (StmtIf e stmts Nothing loc) = do
    --     let e' = apply s e
    --     let stmts' = apply s stmts
    --     StmtIf e' stmts' Nothing loc
    apply s (StmtIf e stmts els loc) = do
        let e' = apply s e
        let stmts' = apply s stmts
        let els' = apply s els
        StmtIf e' stmts' els' loc
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
    apply s (FunCall id es (Just t)) = do
        let es' = apply s es
        FunCall id es' (Just $ apply s t)
    apply s (FunCall id es Nothing) = 
        let es' = apply s es in
        FunCall id es' Nothing
    ftv (FunCall (ID locA name locB) es (Just t)) = ftv t
    ftv _ = undefined


newSPLVar :: TI SPLType
newSPLVar =
    do  (s,overloaded) <- get
        put (s+1,overloaded)
        return $ IdType (idLocCreator ('a':show s))


newSPLVarLoc :: Loc -> TI SPLType
newSPLVarLoc loc =
    do  (s,overloaded) <- get
        put (s+1,overloaded)
        return $ IdType (ID loc ('a':show s) loc )

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
    mgu (BracketType a) (BracketType b) = mgu a b
    mgu (BracketType a) b = mgu a b
    mgu a (BracketType b) = mgu a b

    mgu (FunType arg ret) (FunType arg' ret') = do
        s1 <- mgu arg arg'
        s2 <- mgu (apply s1 ret) (apply s1 ret')
        return (s2 `composeSubst` s1)

    -- mgu (FunType arg ret) t1 = confess $ generateError (FunType arg ret) t1
    -- mgu t1 (FunType arg ret) = confess $ generateError (FunType arg ret) t1
    -- mgu (IdType id) r | not $ isFunctionType r = varBind id r
    -- mgu l (IdType id) | not $ isFunctionType l = varBind id l

    mgu (TypeBasic _ x _) (TypeBasic _ y _) | x == y = return nullSubst

    mgu (Void _ _) (Void _ _) = return nullSubst

    mgu (TupleType  _ (l1,r1) _) (TupleType _ (l2,r2) _) = do
        s1 <- mgu l1 l2
        s2 <- mgu r1 r2
        return (s1 `composeSubst` s2)
    mgu (ArrayType _ x _) (ArrayType _ y _) = mgu x y

    mgu (IdType id) r = varBind id r
    mgu l (IdType id) = varBind id l

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
    case getDLoc id `compare` getDLoc t of
        EQ -> dictate (ErrorD (getDLoc t) ("These types can not be bound\n Occurs check fails: " ++ pp id ++ " vs. " ++ pp t))
        LT -> dictate (ErrorD (getDLoc t) ("These types can not be bound\n Occurs check fails: " ++ pp id ++ " vs. " ++ pp t))
        GT -> dictate (ErrorD (getDLoc id) ("These types can not be bound\n Occurs check fails: " ++ pp id ++ " vs. " ++ pp t))
    >> return nullSubst
varBind id t = return $ Map.singleton id t

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
        funcToStuff (FunCall id args (Just (FunType t t'))) | "_" `isPrefixOf` pp id = 
            (id,FunCall id args (Just (FunType t t')), FunType t t' ) 

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
    let env' = TImisc.insert env (idLocCreator "isEmpty") (generalize env isEmptyType) GlobalScope

    t2 <- newSPLVar
    let printType = FunType t2 (Void defaultLoc defaultLoc)
    let env'' = TImisc.insert env' (idLocCreator "print") (generalize env' printType) GlobalScope
    return env''

std = Set.fromList ["isEmpty","print"]

builtin (ID _ id _) = Set.member id std

-- ===================== Printing ============================
printEnv :: TypeEnv -> String
printEnv (TypeEnv env) = printEnv1 (Map.toList env)

-- printEnv1 :: [(IDLoc, (Scheme,Scope))] -> String
-- printEnv1 [] = ""
-- printEnv1 ((ID _ id _,(Scheme v t,GlobalScope)):xs) = id ++" :: " ++ pp t ++", "++ pp v ++ " Global\n"++ printEnv1 xs
-- printEnv1 ((ID _ id _,(Scheme v t,LocalScope)):xs) = id ++" :: " ++ pp t ++", "++ pp v ++ " Local\n"++ printEnv1 xs
-- printEnv1 ((ID _ id _,(Scheme v t,ArgScope)):xs) = id ++" :: " ++ pp t ++", "++ pp v ++ " arg\n"++ printEnv1 xs
-- printEnv1 ((ID _ id _,(OverScheme v t _ _,LocalScope)):xs) = id ++" :: " ++ pp t ++", "++ pp v ++ " over Local\n"++ printEnv1 xs
-- printEnv1 ((ID _ id _,(OverScheme v t _ _,GlobalScope)):xs) = id ++" :: " ++ pp t ++", "++ pp v ++ " over Global\n"++ printEnv1 xs
-- printEnv1 ((ID _ id _,(OverScheme v t _ _,ArgScope)):xs) = id ++" :: " ++ pp t ++ ", "++ pp v ++ " over arg\n"++ printEnv1 xs


printEnv1 :: [(IDLoc, (Scheme,Scope))] -> String
printEnv1 [] = ""
printEnv1 ((ID _ id _,(Scheme v t,GlobalScope)):xs) = id ++" :: " ++ pp t ++", Global\n"++ printEnv1 xs
printEnv1 ((ID _ id _,(Scheme v t,LocalScope)):xs) = id ++" :: " ++ pp t ++", Local\n"++ printEnv1 xs
printEnv1 ((ID _ id _,(Scheme v t,ArgScope)):xs) = id ++" :: " ++ pp t ++", arg\n"++ printEnv1 xs
printEnv1 ((ID _ id _,(OverScheme v t _ _,LocalScope)):xs) = id ++" :: " ++ pp t ++", over Local\n"++ printEnv1 xs
printEnv1 ((ID _ id _,(OverScheme v t _ _,GlobalScope)):xs) = id ++" :: " ++ pp t ++", over Global\n"++ printEnv1 xs
printEnv1 ((ID _ id _,(OverScheme v t _ _,ArgScope)):xs) = id ++" :: " ++ pp t ++ ", over arg\n"++ printEnv1 xs



printSubst :: [(IDLoc,SPLType)] -> String
printSubst [] = ""
printSubst ((ID _ id _,t):xs) = id ++ " -> " ++ pp t ++ "\n"++ printSubst xs


