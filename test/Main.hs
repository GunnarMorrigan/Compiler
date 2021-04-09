module Main where

import Test.HUnit

import TITest
import ParserTest
import LexerTest

main = do
    putStr "Lexer Tests: \n"
    runTestTT $ TestList lexerTests
    putStr "\nParser Tests: \n"
    runTestTT $ TestList parserTests
    putStr "\nTI Tests: \n"
    runTestTT $ TestList tiTests

