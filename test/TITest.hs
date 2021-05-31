module TITest where
import Test.HUnit

import Control.Monad
import Data.Map as Map
import Data.List as List
import Data.These

import Error
import AST
import Lexer
import Parser
import MutRec
import ReturnGraph
import TImisc
import TI

import System.Directory
import System.IO.Unsafe

-- ====== Tests regarding getType ======
getTypeTest1 = TestCase (assertEq "getType test 1" expected f)
    where
        f = let (res, s) = runTI (getType (IdType (idLocCreator "hoi")) [Head defaultLoc defaultLoc, Snd defaultLoc defaultLoc, Head defaultLoc defaultLoc] )
            in case res of
                This err  -> Left err
                These a b -> Left a
                That (subst, t, ret) -> Right (t, ret)
        expected = Right (ArrayType defaultLoc (TupleType defaultLoc (IdType (ID defaultLoc "a1" defaultLoc),ArrayType defaultLoc (IdType (ID defaultLoc "a3" defaultLoc)) defaultLoc) defaultLoc) defaultLoc,IdType (ID defaultLoc "a3" defaultLoc))
        
getTypeTest2 = TestCase (assertEq "getType test 2" expected f)
    where
        f = let (res, s) = runTI (getType (IdType (idLocCreator "hoi")) [] )
            in case res of
                This err  -> Left err
                These a b -> Left a
                That (subst, t, ret) -> Right (t, ret)
        expected = Right (IdType (ID defaultLoc "a0" defaultLoc),IdType (ID defaultLoc "a0" defaultLoc))

getTypeTests = [TestLabel "getTypeTest1" getTypeTest1, TestLabel "getTypeTest2" getTypeTest2]


-- ====== Tests regarding tiExp ======
expTest1 = TestCase (assertEqual "tiExp test 1" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv Map.empty) (ExpId (idLocCreator "hoi") (Field [Head defaultLoc defaultLoc, Snd defaultLoc defaultLoc, Head defaultLoc defaultLoc]))) in res
        expected = These (ErrorD (DLoc defaultLoc defaultLoc) "Variable: 'hoi', referenced on Line -1 and, Col -1, has not been defined yet. (i.e. reference before declaration)") (empty, IdType (ID defaultLoc "a0" defaultLoc),ExpId (ID defaultLoc "hoi" defaultLoc) (Field [Head defaultLoc defaultLoc,Snd defaultLoc defaultLoc,Head defaultLoc defaultLoc]))

-- expTest2 = TestCase (assertEqual "tiExp test 2" expected f)
--     where
--         f = let (res, s) = runTI (tiExp (TypeEnv (Map.fromList [(idLocCreator "hoi", (Scheme [] (IdType (idLocCreator "z")),LocalScope))] )) (ExpId (idLocCreator "hoi") (Field [Head defaultLoc defaultLoc, Snd defaultLoc defaultLoc, Head defaultLoc defaultLoc])))
--             in res
--         expected = That (fromList [ (idLocCreator "z", ArrayType defaultLoc (TupleType defaultLoc (IdType (idLocCreator "b") , ArrayType  defaultLoc(IdType (idLocCreator "d")) defaultLoc) defaultLoc) defaultLoc)], IdType (idLocCreator "d"))

expTest3 = TestCase (assertEqual "tiExp test 3" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv (Map.fromList [(idLocCreator "hoi", (Scheme [] (ArrayType defaultLoc (TupleType defaultLoc (IdType (idLocCreator "z") ,ArrayType defaultLoc (IdType (idLocCreator "x")) defaultLoc ) defaultLoc) defaultLoc),LocalScope) )] )) (ExpId (idLocCreator "hoi") (Field [Head defaultLoc defaultLoc, Snd defaultLoc defaultLoc, Head defaultLoc defaultLoc])))
            in res
        expected = That (fromList [(ID defaultLoc "a0" defaultLoc,TupleType defaultLoc (IdType (ID defaultLoc "z" defaultLoc),ArrayType defaultLoc (IdType (ID defaultLoc "x" defaultLoc)) defaultLoc) defaultLoc)],IdType (ID defaultLoc "a3" defaultLoc),ExpId (ID defaultLoc "hoi" defaultLoc) (Field [Head defaultLoc defaultLoc,Snd defaultLoc defaultLoc,Head defaultLoc defaultLoc]))
expTest4 = TestCase (assertEqual "tiExp test 4" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv Map.empty) $ ExpEmptyList defaultLoc defaultLoc)
            in res
        expected = That (nullSubst, ArrayType defaultLoc (IdType (ID defaultLoc "a0" defaultLoc)) defaultLoc,ExpEmptyList defaultLoc defaultLoc)

expTest5 = TestCase (assertEqual "tiExp test 5" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv Map.empty) (ExpOp1 defaultLoc Neg (ExpInt defaultLoc 10 defaultLoc) defaultLoc))
            in res
        expected = That (nullSubst,TypeBasic defaultLoc BasicInt defaultLoc, ExpOp1 defaultLoc Neg (ExpInt defaultLoc 10 defaultLoc) defaultLoc)

expTest6 = TestCase (assertEqual "tiExp test 6" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv (Map.fromList [(idLocCreator "hoi", (Scheme [] (TypeBasic defaultLoc BasicBool defaultLoc), LocalScope ) )])) (ExpOp1 defaultLoc Not (ExpId (idLocCreator "hoi") (Field [])) defaultLoc))
            in res
        expected = That (nullSubst,TypeBasic defaultLoc BasicBool defaultLoc,ExpOp1 defaultLoc Not (ExpId (idLocCreator "hoi") (Field [])) defaultLoc)

-- env = 
--     [
--     (idLocCreator "tuple", Scheme [] (IdType (idLocCreator "x") Nothing))
--     ]

-- expTest8 =
--     let (res, s) = runTI (tiExp (TypeEnv (Map.fromList env))  (ExpTuple ( ExpId (idLocCreator "tuple") (Field [Snd defaultLoc ]), ExpId (idLocCreator "tuple") (Field [Fst defaultLoc]) ) (Loc 0 0)) )
--     in case res of
--          Left err ->  putStrLn $ "error: " ++ show err
--          Right (subst, t) ->  putStrLn $ show subst ++ "\n\n" ++ show t

tiExpTests = 
    [TestLabel "expTest1" expTest1,
    -- TestLabel "expTest2" expTest2,
    TestLabel "expTest3" expTest3,
    TestLabel "expTest4" expTest4,
    TestLabel "expTest5" expTest5,
    TestLabel "expTest6" expTest6
    ]


-- ====== Tests regarding tiStmts ======

-- ("flip" :: ID, Scheme [] (TypeBasic BasicBool)),

env' :: [(ID, Scheme)]
env' = 
    [
    ("Fst" :: ID, Scheme [] (IdType (idLocCreator "x"))),
    ("sec" :: ID, Scheme [] (IdType (idLocCreator "y"))),
    ("tuple" :: ID, Scheme [] (IdType (idLocCreator "z")))
    ]

env'' = 
    [(idLocCreator "tuple" , (Scheme [] (IdType (idLocCreator "z")),LocalScope))
    ]

stmtsTest1 stmts = TestCase (assertEqual "tiStmts test 1" expected f)
    where 
        f =   
            let (res, s) = runTI (tiStmt (TypeEnv (Map.fromList env'')) (head stmts) )
            in res
        expected = undefined 


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
fundecl = FunDecl (idLocCreator "swap") [idLocCreator "tuple"] Nothing [] 
        [StmtAssignVar (idLocCreator "tuple") (Field [Snd  defaultLoc defaultLoc]) (ExpId (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc])) Nothing,
        StmtAssignVar (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc]) (ExpId (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc])) Nothing,
        StmtReturn (Just (ExpId (idLocCreator "tuple") (Field []))) defaultLoc]
fundecl' = FunDecl (idLocCreator "swap") [idLocCreator "tuple"] Nothing [] 
    [StmtAssignVar (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc]) (ExpId (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc])) Nothing,
    StmtAssignVar (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc]) (ExpId (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc])) Nothing]
fundecl'' = FunDecl (idLocCreator "swap") [idLocCreator "tuple"] Nothing [VarDeclVar (idLocCreator "tmp") (ExpId (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc]))] 
    [StmtAssignVar (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc]) (ExpId (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc])) Nothing,
    StmtAssignVar (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc]) (ExpId (idLocCreator "tmp") (Field [])) Nothing]

fundecl''' = FunDecl (idLocCreator "swap") [idLocCreator "tuple"] Nothing [VarDeclVar (idLocCreator "tmp") (ExpId (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc]))] 
    [StmtAssignVar (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc]) (ExpId (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc])) Nothing,
    StmtAssignVar (idLocCreator "tuple") (Field [Snd defaultLoc defaultLoc]) (ExpId (idLocCreator "tmp") (Field [])) Nothing,
    StmtReturn (Just (ExpId (idLocCreator "tuple") (Field []))) defaultLoc]

funDeclTest1 ::  IO()
funDeclTest1 = let (res, s) = runTI (tiFunDecl (TypeEnv Map.empty) fundecl''' )
    in case res of
        This err ->  putStrLn $ "error: " ++ show err
        That (subst, TypeEnv env, x) -> do 
            print env 
            putStr $ pp x



-- ====== Tests with full SPL code ======

-- tiTest1 = TestCase $ do
--       file <- readFile  "./test/AutoTestSPL/test1.spl"
--       expected <- readFile  "./test/AutoTestSPL/test1_expected.spl"
--       case tokeniseAndParse mainSegments file of 
--             Right (x, _) -> do
--                   assertEqual "ti test 1" expected (pp x)
--             Left x -> do
--                   assertFailure $ show x ++ "\n" ++ showPlaceOfError file x

-- tiSPLTests = 
--     [
--     -- TestLabel "Ti Test 1" tiTest1,
--     -- TestLabel "Ti Test 2" tiTest2
--     ]

-- ==================== Generic testing for success ====================



{-# NOINLINE tiTestsOnGivenFiles #-}
tiTestsOnGivenFiles = unsafePerformIO $
      do
      failing <-  getDirectoryContents "./test/TI/fail/"
      let fails = List.filter (isSuffixOf "shouldfail.spl") failing
      succeeding <-  getDirectoryContents "./test/TI/success/"
      let succs = List.filter (\x -> not  ("shouldfail.spl" `isSuffixOf` x) && ".spl" `isSuffixOf` x ) succeeding
      return $
            Prelude.map tiTestsFailing fails 
            ++ 
            Prelude.map tiTestsSucceeding succs



tiTestsFailing filepath = TestLabel ("TI test " ++ filepath) $ TestCase $ do
      file <- readFile ("./test/TI/fail/" ++ filepath)
      case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= rtga >>= typeInference of
            Left x -> return ()
            Right _ -> do
                  assertFailure $ "Should not be able to type:\n"++ filepath ++"\n"

tiTestsSucceeding filepath = TestLabel ("TI test " ++ filepath) $ TestCase $ do
      file <- readFile ("./test/TI/success/" ++ filepath)
      case tokeniseAndParse mainSegments file >>= (mutRec . fst) >>= rtga >>= typeInference of
            Left x -> do
                  assertFailure $ "Should be able to type:\n"++ filepath ++"\nBut got the following errors:\n" ++ showError file x
            Right _ -> return ()






-- ==================== End ====================

assertEq :: Show a => String -> Either a (SPLType, SPLType) -> Either a (SPLType, SPLType) -> Assertion
assertEq preface expected actual = do
    let Right (t,ret) = expected
    let Right (t',ret') = actual
    unless (t == t' && ret == ret') (assertFailure msg)
    where msg = (if Prelude.null preface then "" else preface ++ "\n") ++
            "expected: " ++ show expected ++ "\n but got: " ++ show actual



tiTests = 
    getTypeTests 
    ++ tiExpTests
    -- ++ tiSPLTests
    ++ tiTestsOnGivenFiles