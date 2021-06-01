module ParserTest where
import Test.HUnit

import Control.Monad

import Data.Map as Map
import Data.List as DL
import Data.Either

import Error
import Lexer
import Parser
import AST

import System.Directory
import System.IO.Unsafe

-- ==================== Parser checks that test full output ====================
parserTest1 =  TestCase $ do
    file <- readFile  "./test/AutoTestSPL/test1.spl"
    expected <- readFile  "./test/AutoTestSPL/test1_expected.spl"
    case tokeniseAndParse mainSegments file of
        Right (x, _) -> do
            assertEqual "Parser test 1" expected (pp x)
        Left x -> do
            assertFailure $ show x ++ "\n" ++ showPlaceOfError file x


parserTest2 = TestCase $ do
    file <- readFile  "./test/AutoTestSPL/test2.spl"
    expected <- readFile  "./test/AutoTestSPL/test2_expected.spl"
    case tokeniseAndParse mainSegments file of
        Right (x, _) -> do
            assertEqual "Parser test 2" expected (pp x)
        Left x -> do
            assertFailure $ show x ++ "\n" ++ showPlaceOfError file x

-- ==================== Type parser tests (for extension currying/higher order) ====================
{-# NOINLINE parserTypeTests #-}
parserTypeTests = unsafePerformIO $ do
    file <- readFile  "./test/parser/extension/types.spl"
    let content = lines file
    let (errs,tokenTypes) = partitionEithers $ Prelude.map runTokenise content
    if Prelude.null errs
        then return $ zipWith (curry parserTypeTest) content tokenTypes
        else assertFailure $ showError file (Prelude.foldr1 (<>) errs)

parserTypeTest (text,tokens) = TestLabel ("Parser type tests "++ text) $ TestCase $ do
    case run funType tokens of
        Right (x, _) ->
            assertEqual "" text (pp x)
            -- assertEqual "ti test 2" expected (pp x)
        Left x -> do
            assertFailure $ show x


-- ==================== Generic parser tests ====================
{-# NOINLINE parserTestsOnGivenFiles #-}
parserTestsOnGivenFiles = unsafePerformIO $
    do
    spls <-  getDirectoryContents "./test/parser/"
    let fails = DL.filter (isSuffixOf "shouldfail.spl") spls
    let succs = DL.filter (\x -> not  ("shouldfail.spl" `isSuffixOf` x) && ".spl" `isSuffixOf` x ) spls
    return $
        Prelude.map parserTestsFailing fails ++
        Prelude.map parserTestsSucceeding succs


parserTestsFailing filepath = TestLabel ("Parser test " ++ filepath) $ TestCase $ do
    file <- readFile ("./test/parser/" ++ filepath)
    case tokeniseAndParse mainSegments file of
        Left x -> return ()
        Right (x, _) -> do
            assertFailure $ "Should not be able to parse:\n"++ filepath ++"\n"

parserTestsSucceeding filepath = TestLabel ("Parser test " ++ filepath) $ TestCase $ do
    file <- readFile ("./test/parser/" ++ filepath)
    case tokeniseAndParse mainSegments file of
        Left x -> do
            assertFailure $ "Should be able to parse:\n"++ filepath ++"\n"
        Right (x, _) -> return ()


-- We are too slow for this test case
-- parserTestsS = TestCase $ do
--       file <- readFile "./test/parser/tooSlow/x.spl"
--       case tokeniseAndParse mainSegments file of
--             Left x -> do
--                   assertFailure $ "Should be able to parse:\n"++ "./test/parser/tooSlow/x.spl" ++"\n"
--             Right (x, _) -> assertBool "" True 


parserTests =
    [ TestLabel "Parser Test 1" parserTest1
    , TestLabel "Parser Test 2" parserTest2
    ]
    ++
    parserTestsOnGivenFiles
    ++
    parserTypeTests