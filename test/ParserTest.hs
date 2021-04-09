module ParserTest where
import Test.HUnit

import Control.Monad
import Data.Map as Map
import System.Directory

import Parser
import AST

-- main :: IO()
parserTest1 = TestCase $ do
       file <- readFile  "test/AutoTestSpl/test1.spl"
       case tokeniseAndParse mainSegments file of 
              Right (x, _) -> do
                    assertEqual "parser test 1" file (pp x)
              Left x -> do
                    assertFailure $ show x

parserTests = [parserTest1]