module TITest where
import Test.HUnit

import Control.Monad
import Data.Map as Map


import Error
import AST
import Lexer
import Parser
import TI

-- ====== Tests regarding getType ======
getTypeTest1 = TestCase (assertEq "getType test 1" expected f)
    where
        f = let (res, s) = runTI (getType (IdType (idLocCreator "hoi") Nothing) [Head, Second, Head] )
            in case res of
                Left err  -> Left err
                Right (subst, t, ret) -> Right (t, ret)
        expected = Right (ArrayType (TupleType (IdType (idLocCreator "a") Nothing, ArrayType (IdType (idLocCreator "b") Nothing) defaultLoc) defaultLoc) defaultLoc, IdType (idLocCreator "b") Nothing)
        
getTypeTest2 = TestCase (assertEq "getType test 2" expected f)
    where
        f = let (res, s) = runTI (getType (IdType (idLocCreator "hoi") Nothing) [] )
            in case res of
                Left err  -> Left err
                Right (subst, t, ret) -> Right (t, ret)
        expected = Right (IdType (idLocCreator "b") Nothing, IdType (idLocCreator "b") Nothing)

getTypeTests = [TestLabel "getTypeTest1" getTypeTest1, TestLabel "getTypeTest2" getTypeTest2]


-- ====== Tests regarding tiExp ======
expTest1 = TestCase (assertEqual "tiExp test 1" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv Map.empty) (ExpId (idLocCreator "hoi") (Field [Head, Second, Head]))) in res
        expected = Left $ Error (-1) (-1) "id: 'hoi', referenced on Line -1 and, Col -1, has not been defined yet: (i.e. reference before declaration)"

expTest2 = TestCase (assertEqual "tiExp test 2" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv (Map.fromList [(idLocCreator "hoi", Scheme [] (IdType (idLocCreator "z") Nothing) )] )) (ExpId (idLocCreator "hoi") (Field [Head, Second, Head])))
            in res
        expected = Right (fromList [ (idLocCreator "z", ArrayType (TupleType (IdType (idLocCreator "b")  Nothing, ArrayType (IdType (idLocCreator "d") Nothing) defaultLoc) defaultLoc) defaultLoc)], IdType (idLocCreator "d") Nothing)

expTest3 = TestCase (assertEqual "tiExp test 3" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv (Map.fromList [(idLocCreator "hoi", Scheme [] (ArrayType (TupleType (IdType (idLocCreator "z") Nothing ,ArrayType (IdType (idLocCreator "x") Nothing) defaultLoc ) defaultLoc) defaultLoc) )] )) (ExpId (idLocCreator "hoi") (Field [Head, Second, Head])))
            in res
        expected = Right (fromList [( idLocCreator "a",TupleType (IdType (idLocCreator "z") Nothing,ArrayType (IdType (idLocCreator "x") Nothing) defaultLoc) defaultLoc)],IdType (idLocCreator "d") Nothing)

expTest4 = TestCase (assertEqual "tiExp test 4" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv Map.empty) ExpEmptyList)
            in res
        expected = Right (empty, ArrayType (IdType (idLocCreator "a") Nothing) defaultLoc)

expTest5 = TestCase (assertEqual "tiExp test 5" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv Map.empty) (ExpOp1 Neg $ ExpInt 10))
            in res
        expected = Right (empty,TypeBasic BasicInt defaultLoc)

expTest6 = TestCase (assertEqual "tiExp test 6" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv (Map.fromList [(idLocCreator "hoi", Scheme [] (TypeBasic BasicBool defaultLoc) )])) (ExpOp1 Not $ ExpId (idLocCreator "hoi") (Field [])))
            in res
        expected = Right (empty,TypeBasic BasicBool defaultLoc)




-- ====== Tests regarding tiStmts ======

-- ("flip" :: ID, Scheme [] (TypeBasic BasicBool)),

env' = 
    [
    ("first" :: ID, Scheme [] (IdType (idLocCreator "x") Nothing)),
    ("sec" :: ID, Scheme [] (IdType (idLocCreator "y") Nothing)),
    ("tuple" :: ID, Scheme [] (IdType (idLocCreator "z") Nothing))
    ]

env'' = 
    [("tuple" :: ID, Scheme [] (IdType (idLocCreator "z") Nothing))
    ]


-- stmtsTest1 :: [Stmt] -> IO()
-- stmtsTest1 stmts = let (res, s) = runTI (tiStmtTest (TypeEnv (Map.fromList env'')) (head stmts) )
--     in case res of
--          Left err ->  putStrLn $ "error: " ++ err
--          Right (subst, t1, t2, env) ->  putStrLn $ show subst 
--             ++ "\n\n" ++ show t1 
--             ++ "\n\n" ++ show t2
--             ++ "\n\n" ++ show env


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
fundecl = FunDecl (idLocCreator "swap") [idLocCreator "tuple"] Nothing [] [StmtDeclareVar (idLocCreator "tuple") (Field [First]) (ExpId (idLocCreator "tuple") (Field [First])),StmtDeclareVar (idLocCreator "tuple") (Field [Second]) (ExpId (idLocCreator "tuple") (Field [Second])),StmtReturn (Just (ExpId (idLocCreator "tuple") (Field [])))]
fundecl' = FunDecl (idLocCreator "swap") [idLocCreator "tuple"] Nothing [] [StmtDeclareVar (idLocCreator "tuple") (Field [First]) (ExpId (idLocCreator "tuple") (Field [Second])),StmtDeclareVar (idLocCreator "tuple") (Field [Second]) (ExpId (idLocCreator "tuple") (Field [First]))]
fundecl'' = FunDecl (idLocCreator "swap") [idLocCreator "tuple"] Nothing [VarDeclVar (idLocCreator "tmp") (ExpId (idLocCreator "tuple") (Field [First]))] [StmtDeclareVar (idLocCreator "tuple") (Field [First]) (ExpId (idLocCreator "tuple") (Field [Second])),StmtDeclareVar (idLocCreator "tuple") (Field [Second]) (ExpId (idLocCreator "tmp") (Field []))]

fundecl''' = FunDecl (idLocCreator "swap") [idLocCreator "tuple"] Nothing [VarDeclVar (idLocCreator "tmp") (ExpId (idLocCreator "tuple") (Field [First]))] [StmtDeclareVar (idLocCreator "tuple") (Field [First]) (ExpId (idLocCreator "tuple") (Field [Second])),StmtDeclareVar (idLocCreator "tuple") (Field [Second]) (ExpId (idLocCreator "tmp") (Field [])),StmtReturn (Just (ExpId (idLocCreator "tuple") (Field [])))]

funDeclTest1 ::  IO()
funDeclTest1 = let (res, s) = runTI (tiFunDecl (TypeEnv Map.empty) fundecl''' )
    in case res of
         Left err ->  putStrLn $ "error: " ++ show err
         Right (TypeEnv env) -> print env



-- ====== Tests with full SPL code ======

-- tiTest1 = TestCase $ do
--       -- path <- getCurrentDirectory
--       -- print path
--       file <- readFile  "./test/AutoTestSPL/test1.spl"
--       case tokeniseAndParse mainSegments file of 
--             Right (x, _) -> do
--                   assertEqual "ti test 1" file (pp x)
--             Left x -> do
--                   assertFailure $ show x ++ "\n" ++ showPlaceOfError file x




showPlaceOfError :: String -> Error -> String
showPlaceOfError code (Error line col msg) =
    lines code !! (line -1) ++ "\n"
    ++ replicate (col-1) ' ' ++ "^"








tiExpTests = 
    [TestLabel "expTest1" expTest1,
    TestLabel "expTest2" expTest2,
    TestLabel "expTest3" expTest3,
    TestLabel "expTest4" expTest4,
    TestLabel "expTest5" expTest5,
    TestLabel "expTest6" expTest6
    ]

assertEq :: Show a => String -> Either a (SPLType, SPLType) -> Either a (SPLType, SPLType) -> Assertion
assertEq preface expected actual = do
    let Right (t,ret) = expected
    let Right (t',ret') = actual
    unless (t `eqType` t' && ret `eqType` ret') (assertFailure msg)
    where msg = (if Prelude.null preface then "" else preface ++ "\n") ++
            "expected: " ++ show expected ++ "\n but got: " ++ show actual



tiTests = getTypeTests ++ tiExpTests