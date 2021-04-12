module ParserTest where
import Test.HUnit

import Control.Monad
import Data.Map as Map
import System.Directory ( getCurrentDirectory )

import Error
import Lexer
import Parser
import AST

-- main :: IO()
parserTest1 = TestCase $ do
      -- path <- getCurrentDirectory
      -- print path
      file <- readFile  "./test/AutoTestSPL/test1.spl"
      expected <- readFile  "./test/AutoTestSPL/test1_expected.spl"
      case tokeniseAndParse mainSegments file of
            Right (x, _) -> do
                  assertEqual "parser test 1" expected (pp x)
            Left x -> do
                  assertFailure $ show x ++ "\n" ++ showPlaceOfError file x

parserTests = [parserTest1]