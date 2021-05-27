module Main where

import Test.HUnit


import LexerTest
import ParserTest
import TITest

main = do
    putStr "Lexer Tests: \n"
    runTestTT $ TestList lexerTests
    putStr "\nParser Tests: \n"
    runTestTT $ TestList parserTests
    putStr "\nTI Tests: \n"
    runTestTT $ TestList tiTests

