{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
module Error where

import AST

import Data.List
import Data.Char
import Control.Applicative

data Error = Error Loc String
  -- deriving (Show)

instance Eq Error where
  (==) (Error (Loc line col) m) (Error (Loc line' col') m') =  line == line' && col == col'

instance Ord Error where
  (Error (Loc line col) m) `compare` (Error (Loc line' col') m') = if line == line' then  col `compare` col' else line `compare` line'

instance Show Error where
  show (Error _ message) = message
  -- show (Error (-1) (-1) message) = message
  -- show (Error (Loc line col) message) = message ++ ", on line: " ++show line ++ " and character: " ++ show col 

instance Alternative (Either Error) where
  empty = Left $ Error (Loc 0 0) ""
  Left x <|> Left y = Left $ max x y
  Left _ <|> e2 = e2
  e1 <|> _ = e1


showPlacesOfErrors :: String -> [Error] -> String
showPlacesOfErrors code' errs = intercalate "\n\n" $ map (showPlaceOfError code') errs


showPlaceOfError :: String -> Error -> String
showPlaceOfError code' (Error (Loc (-1) (-1)) msg) = msg
showPlaceOfError code' (Error (Loc line col) msg) =
    
    let code = replaceTab code' in
    msg ++ "\n" ++
    (if line == 1 then "" else lines code !! (line - 2) ++ "\n" )
    ++ lines code !! (line - 1) ++ "\n"
    ++ replicate (if col > 2 then col-2 else 0) ' ' ++ "^^^\n"
    ++ if length code > line then lines code !! line ++ "\n" else ""

replaceTab :: String -> String
replaceTab [] = []
replaceTab (x:xs) | x== '\t' = "    " ++ replaceTab xs
replaceTab (x:xs)  = x:replaceTab xs

defaultLoc :: Loc
defaultLoc = Loc (-1) (-1)

-- ========== Parser Errors ==========
missingSeparator loc sepToken token = Error loc ("Expected separator '"++ show sepToken ++ "' but found '" ++ show token ++ "' on " ++ show loc)
unexpectedToken expected found loc = Error loc ("Expected: '"++show expected++"' but found: '" ++ show found ++ "' on " ++ show loc)
unexpectedEOF expected = Error (Loc (-1) (-1)) ("Unexpected EOF, expected: "++show expected++".")

-- ========== Parser Errors ==========
missingReturn :: ID -> SPLType  -> Loc -> Error
missingReturn fName t loc = Error loc ("Missing return statement in function '" ++ fName ++ "' on " ++ show loc ++ ", expected return statement of type " ++ pp t ++ " but got no return, please add a return statement to the function")  
conflictingReturn :: ID -> Loc -> Error 
conflictingReturn fName loc = Error loc ("Found conflicting return types on " ++ show loc ++", types Void and non Void for function '" ++ fName ++ "'") 
expectedReturn :: ID -> SPLType -> String -> Loc -> Error
expectedReturn fName expect got loc = Error loc ("Expected function '" ++ fName ++ "' on " ++ show loc ++ " to return " ++ pp expect ++" but returned " ++ got)

-- ========== TI Errors ==========
refBeforeDec :: (LOC a, PrettyPrinter a) => String -> a -> Error
refBeforeDec s id = Error (getLoc id) (s++"'" ++ pp id ++ "', referenced " ++ showLoc id ++ ", has not been defined yet. (i.e. reference before declaration)")

doubleDef id = Error (getLoc id) ("Variable: " ++ showIDLoc id ++ ", already exists in the type environment. (i.e. double decleration)")

funcCallMoreArgs id = Error (getLoc id) ("Function: '" ++ pp id ++ "',  " ++ showLoc id ++ ", called with too many arguments.")
funcCallLessArgs id = Error (getLoc id) ("Function: '" ++ pp id ++ "',  " ++ showLoc id ++ ", called with too many arguments.")