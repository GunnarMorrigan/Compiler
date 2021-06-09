module GenTest where
import Test.HUnit

import Control.Monad
import Data.Map as Map
import Data.List as DL
import Data.These


import AST
import Gen

import System.Directory
import System.IO.Unsafe
import System.Process

-- ====== Running tests ======
runSSM = do 
    output <- readProcess "../ssm.bat" ["test/Gen/e2e/ass.ssm"] ""
    let lined = lines output
    let output = DL.drop 2 $ DL.take (length lined - 1) lined
    return output

-- {-# NOINLINE e2eTests #-}
-- e2eTests = unsafePerformIO $
--     do
--     spls <-  getDirectoryContents "./test/Gen/e2e/"
--     let e2es = DL.filter (isSuffixOf ".spl") spls
--     return $ Prelude.map e2eTest e2es
        -- Prelude.map parserTestsSucceeding succs

e2eTest = TestLabel "E2E test test1.spl" $ TestCase $ do
    file <- readFile "./test/Gen/e2e/test1.spl"
    case tokenizeParserTIGen file of
        Right ssm -> do 
            writeFile "test/Gen/e2e/ass.ssm" (pp ssm)
            output <- runSSM
            assertEqual "E2E test test1.spl" expected output
        Left err -> assertFailure $ show err
    where expected = [""]


genTests =
    [e2eTest]
    