module ReturnGraph where

import Lexer
import AST
import Data.Bifunctor
import Parser
import TI
import Data.Map as Map
import Error

class ReturnGraph a where
    rtga :: a -> Either Error a

-- instance (ReturnGraph a, PrettyPrinter a) => ReturnGraph [a] where
--     rtga [] _ = Right ([], [Void])
--     rtga [x] env = first (:[]) <$> returnGraph x env
--     rtga (x:xs) env = do
--         (f, t) <- rtga x env
--         (s, t') <- rtga xs env
--         if t==t'    then return (f:s, t) 
--                     else Left (Error (-1) (-1) $ "Function '" ++ pp f ++ "' has different (implicit) return types: '" ++ pp t ++ "' and '" ++ pp t' ++ "'")

instance ReturnGraph SPL where
    rtga (SPL []) = Right (SPL [])
    rtga (SPL (x:xs)) = (\(SPL xs) (SPL ys)-> SPL $ xs ++ ys) <$> ((\x->SPL [x]) <$> rtga x) <*> rtga (SPL xs)

instance ReturnGraph Decl where
    rtga (FuncMain x) = FuncMain <$> rtga x
    rtga x = Right x  

instance ReturnGraph FunDecl where
    rtga (FunDecl fname args ftype vars stmts) = case rtgaStmts stmts of
        Nothing -> Right (FunDecl fname args ftype vars stmts)
        Just (Error a b x) -> Left (Error a b x)

rtgaStmtsForLevel :: [Stmt] -> Either Error Bool
rtgaStmtsForLevel stmts = case Prelude.filter isValidReturn stmts of
            [] -> Right True
            xs -> if allTheSame (Prelude.map isVoidReturn xs) then Right (isVoidReturn $ head xs) else Left $ Error 0 0 "Found void and type return"

isVoidReturn :: Stmt ->  Bool
isVoidReturn (StmtReturn Nothing _) = True
isVoidReturn (StmtIf a (x:xs) b loc) = if isValidReturn x then isVoidReturn x else isVoidReturn (StmtIf a xs b loc)
isVoidReturn _ = False

isValidReturn :: Stmt  -> Bool
isValidReturn (StmtReturn _ _) = True
isValidReturn (StmtIf _ iStmts els _) = case els of
    Nothing -> False 
    Just eStmts -> any isValidReturn iStmts && any isValidReturn eStmts
isValidReturn _ = False

rtgaStmts :: [Stmt]  -> Maybe Error
rtgaStmts [] = Nothing
rtgaStmts stmts = case rtgaStmtsForLevel stmts of
    Left x-> Just x
    Right x -> checkReturns stmts x
    
checkReturns :: [Stmt] -> Bool -> Maybe Error
checkReturns [] expect = Nothing
checkReturns (x:xs) expect = case x of
    (StmtIf _ istmts els _) -> case checkReturns istmts expect of
        Nothing -> case els of
            Nothing -> checkReturns xs expect
            Just estmts -> case checkReturns estmts expect of
                Nothing -> checkReturns xs expect
                Just error -> Just error
        Just error -> Just error
    (StmtReturn e (Loc line col)) -> if isVoidReturn x == expect 
        then checkReturns xs expect 
        else Just $ Error line col $ "Found invalid return: '" ++ pp x ++ "' expected function to be " ++ if isVoidReturn x then "non Void" else "Void"
    (StmtWhile e wstmts _) -> case checkReturns wstmts expect of
        Nothing -> checkReturns xs expect
        Just error -> Just error
    _ -> checkReturns xs expect

-- rtgaStmts (x:xs) expect = case x of
--     (StmtReturn e) -> case e of
--         Nothing -> Right $ Just False 
--         Just _ -> Right $ Just True
--     (StmtWhile e stmts) -> case rtgaStmts stmts expect of
--         Left x -> Left x
--         Right Nothing -> rtgaStmts xs expect
--         Right (Just exp) -> case expect of
--             Nothing -> rtgaStmts xs (Just True)
--             Just a -> if a == exp then rtgaStmts xs expect else Left $ Error 0 0 "lalala"
--     (StmtIf e stmts Nothing) -> case rtgaStmts stmts expect of
--         Left x -> Left x
--         Right Nothing -> rtgaStmts xs expect
--         Right (Just exp) -> case expect of
--             Nothing -> rtgaStmts xs (Just True)
--             Just a -> if a == exp then rtgaStmts xs expect else Left $ Error 0 0 "lalala" 
--     StmtDeclareVar {} -> rtgaStmts xs expect
--     StmtFuncCall  {} -> rtgaStmts xs expect
-- rtgaStmts [x] = case x of 
--     (StmtIf e stmts Nothing) -> rtgaStmts stmts
--     (StmtIf e stmts (Just els)) -> if rtgaStmts stmts == rtgaStmts els then rtgaStmts stmts else Left $ Error 0 0 "no same return for if else"
--     (StmtWhile e stmts) -> undefined 
--     (StmtDeclareVar id field exp) -> undefined
--     (StmtFuncCall f) -> undefined 
--     (StmtReturn e) -> case e of 
--         Nothing -> Right False
--         Just x -> Right True
-- rtgaStmts 

-- instance ReturnGraph Decl where
--     -- returnGraph (FuncMain x) env = first FuncMain <$> returnGraph x env
--     rtga (MutRec []) env = undefined
--     rtga (MutRec (x:xs)) env = undefined
--     rtga x env = Right(x, [Void])

-- instance ReturnGraph FunDecl where
--     returnGraph (FunDecl id a _ b xs) env = --Right (FunDecl id a (Just ftype) b xs, [ftype]) 



-- Checks if it holds that the function returns a void or a type on every return, 
--  returns Error if there are incompatible returns i.e. void and other type
--  returns Right True if there is a same return type
--  returns Right False if there is no or an empty return statement
-- checkReturns :: [Stmt] -> Either Error [SPLType]
-- checkReturns [] = Right []
-- checkReturns (x:xs) = case x of
--     StmtIf _ stmts Nothing -> (++) <$> checkReturns stmts <*> checkReturns xs
--     StmtIf _ stmts (Just e) -> (\a b c -> a ++ b ++ c) <$> checkReturns stmts <*> checkReturns e <*> checkReturns xs
--     StmtWhile _ stmts -> (++) <$> checkReturns stmts <*> checkReturns xs
--     StmtDeclareVar {} -> checkReturns xs
--     StmtFuncCall  {} -> checkReturns xs
--     StmtReturn (Just e) -> f $ (:) <$> Right (runTI ) <*> checkReturns xs 
--     StmtReturn Nothing -> f $ (:) <$> Right False <*> checkReturns xs 
--     where   f (Right list) = if allTheSame list then Right list else Left (Error 0 0 $ "Found incompatible returns in function '" ++ pp x ++ "'")
--             f x = x
allTheSame :: (Eq a) => [a] -> Bool
allTheSame [] = True
allTheSame xs = all (== head xs) (tail xs)

gMain1 :: String -> IO()
gMain1 filename = do
       file <- readFile $ splFilePath++filename
       case tokeniseAndParse mainSegments file of 
              Right (a, _) -> case gHelp a of
                  Right x -> print $ rtga a
                  Left x -> do print x
              Left x -> do print x

gHelp :: SPL -> Either Error (Map IDLoc Scheme)
gHelp code = let (res, s) = runTI (tiSPL (TypeEnv Map.empty) code )
    in case res of
            Right (TypeEnv env) -> Right env
            (Left (Error a b x)) -> Left (Error a b x)


