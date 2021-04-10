module ParserTest where
import Test.HUnit

import Control.Monad
import Data.Map as Map
import System.Directory ( getCurrentDirectory )

import Lexer
import Parser
import AST

-- main :: IO()
parserTest1 = TestCase $ do
      -- path <- getCurrentDirectory
      -- print path
      file <- readFile  "./test/AutoTestSPL/test1.spl"
      case tokeniseAndParse mainSegments file of 
            Right (x, _) -> do
                  assertEqual "parser test 1" file (pp x)
            Left x -> do
                  assertFailure $ show x ++ "\n" ++ showPlaceOfError file x




showPlaceOfError :: String -> Error -> String
showPlaceOfError code (Error line col msg) =
    lines code !! (line -1) ++ "\n"
    ++ replicate (col-1) ' ' ++ "^"




parserTests = [parserTest1]