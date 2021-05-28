module LexerTest where
import Test.HUnit

import Control.Monad
import Data.Map as Map
import Data.List as List

import Error
import AST
import Lexer
-- import Parser


import System.Directory
import System.IO.Unsafe


{-# NOINLINE tiTestsOnGivenFiles #-}
tiTestsOnGivenFiles = unsafePerformIO $
      do
      failing <-  getDirectoryContents "./test/lexer/"
      let fails = List.filter (isSuffixOf "shouldfail.spl") failing
      succeeding <-  getDirectoryContents "./test/lexer/"
      let succs = List.filter (\x -> not  ("shouldfail.spl" `isSuffixOf` x) && ".spl" `isSuffixOf` x ) succeeding
      return $
            Prelude.map tiTestsFailing fails 
            ++ 
            Prelude.map tiTestsSucceeding succs



tiTestsFailing filepath = TestLabel ("Lexer test " ++ filepath) $ TestCase $ do
      file <- readFile ("./test/lexer/" ++ filepath)
      case runTokenise file of
            Left x -> return ()
            Right _ -> do
                  assertFailure $ "Should not be able to tokenise:\n"++ filepath ++"\n"

tiTestsSucceeding filepath = TestLabel ("Lexer test " ++ filepath) $ TestCase $ do
      file <- readFile ("./test/lexer/" ++ filepath)
      case runTokenise file of
            Left x -> do
                  assertFailure $ "Should be able to tokenise:\n"++ filepath ++"\nBut got the following errors:\n" ++ showError file x
            Right _ -> return ()






lexerTests = tiTestsOnGivenFiles