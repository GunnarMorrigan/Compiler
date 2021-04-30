module ReturnGraph where

import Lexer
import AST
import Parser
import TI

import Data.Bifunctor
import Data.Map as Map
import Error
import Data.Maybe

class ReturnGraph a where
    rtga :: a -> Either Error a

instance ReturnGraph SPL where
    rtga (SPL []) = Right (SPL [])
    rtga (SPL (x:xs)) = (\(SPL xs) (SPL ys)-> SPL $ xs ++ ys) <$> ((\x->SPL [x]) <$> rtga x) <*> rtga (SPL xs)

instance ReturnGraph Decl where
    rtga (FuncMain x) = FuncMain <$> rtga x
    rtga x = Right x  

instance ReturnGraph FunDecl where
    rtga (FunDecl fname args ftype vars stmts) = case rtgaStmts stmts fname ftype of
        Nothing -> Right (FunDecl fname args ftype vars stmts)
        Just (Error a b x) -> Left (Error a b x)

rtgaStmtsForLevel :: [Stmt] -> IDLoc -> Maybe SPLType -> Either Error Bool
rtgaStmtsForLevel stmts (ID fname (Loc line col)) fType = case Prelude.filter isValidReturn stmts of
            [] -> case fType of
                Nothing -> Right True 
                (Just x) -> case last (getArgsTypes x) of
                    (Void _) -> Right True 
                    t -> Left (missingReturn fname t line col )
            xs ->  if allTheSame (Prelude.map isVoidReturn xs) 
                    then case fType of
                        Nothing -> if allTheSame (Prelude.map isVoidReturn xs) 
                                    then Right (isVoidReturn $ head xs) 
                                    else let l = getLocReturn (last xs) in  Left (conflictingReturn fname l)
                        (Just y) ->  case y of
                            (Void _) -> if isVoidReturn $ head xs
                                    then Right True
                                    else let l = getLocReturn (last xs) in  Left (expectedReturn fname (Void l) "non Void" l)
                            t -> if not (isVoidReturn $ head xs)
                                    then Right False
                                    else let l = getLocReturn(head xs) in Left (expectedReturn fname t "Void" l)
                    else let l = getLocReturn (last xs) in Left $ conflictingReturn fname l



getLocReturn :: Stmt -> Loc 
getLocReturn (StmtReturn _  loc) = loc

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

rtgaStmts :: [Stmt]-> IDLoc -> Maybe SPLType  -> Maybe Error
rtgaStmts [] _ _ = Nothing
rtgaStmts stmts (ID fname (Loc l c)) ftype = case rtgaStmtsForLevel stmts (ID fname (Loc l c)) ftype of
    Left x-> Just x
    Right x -> checkReturns stmts x fname ftype
    
checkReturns :: [Stmt] -> Bool -> ID -> Maybe SPLType -> Maybe Error
checkReturns [] _ _ _ = Nothing
checkReturns (x:xs) expect fName fType = case x of
    (StmtIf _ istmts els _) -> case checkReturns istmts expect fName fType of
        Nothing -> case els of
            Nothing -> checkReturns xs expect fName fType
            Just estmts -> case checkReturns estmts expect fName fType of
                Nothing -> checkReturns xs expect fName fType
                Just error -> Just error
        Just error -> Just error
    (StmtReturn e loc) -> if isVoidReturn x == expect 
        then checkReturns xs expect fName  fType
        else Just (expectedReturn fName (if isVoidReturn x then fromMaybe (Void loc)  fType else Void loc) ((if isVoidReturn x then "Void" else "non Void") ++ ppExp e) loc)
    (StmtWhile e wstmts _) -> case checkReturns wstmts expect fName fType of
        Nothing -> checkReturns xs expect fName fType
        Just error -> Just error
    _ -> checkReturns xs expect fName fType

ppFtype :: Maybe SPLType  -> String
ppFtype Nothing = "non Void"
ppFtype (Just x) = pp x
ppExp :: Maybe Exp -> String 
ppExp Nothing = ""
ppExp (Just e) = ": '" ++ pp e ++ "'"

allTheSame :: (Eq a) => [a] -> Bool
allTheSame [] = True
allTheSame xs = all (== head xs) (tail xs)

gMain1 :: String -> IO()
gMain1 filename = do
       file <- readFile $ splFilePath++filename
       case tokeniseAndParse mainSegments file of 
              Right (a, _) -> case rtga a of
                  Right x -> print $ gHelp a
                  Left x -> do print x
              Left x -> do print x

gHelp :: SPL -> Either Error (Map IDLoc Scheme)
gHelp code = let (res, s) = runTI (tiSPL (TypeEnv Map.empty) code )
    in case res of
            Right (TypeEnv env) -> Right env
            (Left (Error a b x)) -> Left (Error a b x)


