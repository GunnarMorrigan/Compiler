module BTA where

import Parser

function :: SPL -> [ID] -> [ID] -> [ID] -> Either Error (a, [(Token, Int, Int)])
function (SPL (x:xs)) (globVar:vars) =