module Main where

import Test.HUnit


import LexerTest
import ParserTest
import TITest
import GenTest

main = do
    putStr "Lexer Tests: \n"
    runTestTT $ TestList lexerTests
    putStr "\nParser Tests: \n"
    runTestTT $ TestList parserTests
    putStr "\nTI Tests: \n"
    runTestTT $ TestList tiTests
    putStr "\nGen Tests: \n"
    runTestTT $ TestList genTests

