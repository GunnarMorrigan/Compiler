module TITest where
import Test.HUnit

import Control.Monad
import Data.Map as Map

import TI
import AST

-- ====== Tests regarding getType ======
getTypeTest1 = TestCase (assertEq "getType test 1" expected f)
    where
        f = let (res, s) = runTI (getType (IdType (idLocCreator "hoi") Nothing) [Head, Second, Head] )
            in case res of
                Left err  -> Left err
                Right (subst, t, ret) -> Right (t, ret)
        expected = Right (ArrayType (TupleType (IdType (idLocCreator "a") Nothing, ArrayType $ IdType (idLocCreator "b") Nothing)), IdType (idLocCreator "b") Nothing)
        
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
        expected = Left "id: 'hoi', referenced on Line -1 and, Col -1, has not been defined yet: (i.e. reference before declaration)"

expTest2 = TestCase (assertEqual "tiExp test 2" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv (Map.fromList [(idLocCreator "hoi", Scheme [] (IdType (idLocCreator "z") Nothing) )] )) (ExpId (idLocCreator "hoi") (Field [Head, Second, Head])))
            in res
        expected = Right (fromList [ (idLocCreator "z", ArrayType (TupleType (IdType (idLocCreator "b") Nothing,ArrayType (IdType (idLocCreator "d") Nothing))))], IdType (idLocCreator "d") Nothing)


expTest3 = TestCase (assertEqual "tiExp test 3" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv (Map.fromList [(idLocCreator "hoi", Scheme [] (ArrayType (TupleType (IdType (idLocCreator "z") Nothing ,ArrayType (IdType (idLocCreator "x") Nothing)))) )] )) (ExpId (idLocCreator "hoi") (Field [Head, Second, Head])))
            in res
        expected = Right (fromList [( idLocCreator "a",TupleType (IdType (idLocCreator "z") Nothing,ArrayType (IdType (idLocCreator "x") Nothing)))],IdType (idLocCreator "d") Nothing)

expTest4 = TestCase (assertEqual "tiExp test 4" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv Map.empty) ExpEmptyList)
            in res
        expected = Right (empty, ArrayType (IdType (idLocCreator "a") Nothing))

expTest5 = TestCase (assertEqual "tiExp test 5" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv Map.empty) (ExpOp1 Neg $ ExpInt 10))
            in res
        expected = Right (empty,TypeBasic BasicInt)



expTest6 = TestCase (assertEqual "tiExp test 6" expected f)
    where
        f = let (res, s) = runTI (tiExp (TypeEnv (Map.fromList [(idLocCreator "hoi", Scheme [] (TypeBasic BasicBool) )])) (ExpOp1 Not $ ExpId (idLocCreator "hoi") (Field [])))
            in res
        expected = Right (empty,TypeBasic BasicBool)

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