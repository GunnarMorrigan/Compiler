module Try where

import Data.List as DL

import System.Process

runSSM = do 
    output <- readProcess "../ssm.bat" ["./Gen/e2e/ass.ssm"] ""
    let lined = lines output
    let output = DL.drop 2 $ DL.take (length lined - 1) lined
    return output

main = runSSM