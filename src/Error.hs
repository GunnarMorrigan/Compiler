{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
module Error where

import AST

import Data.List
import Data.Char
import Control.Applicative

data Error = Error Int Int String
  -- deriving (Show)

instance Eq Error where
  (==) (Error line col m) (Error line' col' m') =  line == line' && col == col'

instance Ord Error where
  (Error line col m) `compare` (Error line' col' m') = if line == line' then  col `compare` col' else line `compare` line'

instance Show Error where
  show (Error _ _ message) = message
  -- show (Error (-1) (-1) message) = message
  -- show (Error line col message) = message ++ ", on line: " ++show line ++ " and character: " ++ show col 

instance Alternative (Either Error) where
  empty = Left $ Error 0 0 ""
  Left x <|> Left y = Left $ max x y
  Left _ <|> e2 = e2
  e1 <|> _ = e1

showPlaceOfError :: String -> Error -> String
showPlaceOfError code' (Error (-1) (-1) msg) = ""
showPlaceOfError code' (Error line col msg) =
    -- dropWhile isSpace $
    let code = replaceTab code' in
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
missingSeparator line col sepToken token = Error line col ("Expected separator '"++ show sepToken ++ "' but found '" ++ show token ++ "' on Line " ++ show line ++ " and, Col "++ show col ++ ".")
unexpectedToken expected found line col = Error line col ("Expected: '"++show expected++"' but found: '" ++ show found ++ "' on Line " ++ show line ++ " and, Col " ++ show col)
unexpectedEOF expected = Error (-1) (-1) ("Unexpected EOF, expected: "++show expected++".")


-- ========== Parser Errors ==========
missingReturn :: ID -> SPLType  -> Int -> Int -> Error
missingReturn fName t line col = Error line col ("Missing return statement in function '" ++ fName ++ "' on Line " ++ show line ++ " and Col " ++ show col ++ ", expected return statement of type " ++ pp t ++ " but got no return, please add a return statement to the function")  
conflictingReturn :: ID -> Loc -> Error 
conflictingReturn fName (Loc line col) = Error line col ("Found conflicting return types on Line " ++ show line ++ " and Col " ++ show col ++ ", types Void and non Void for function '" ++ fName ++ "'") 
expectedReturn :: ID -> SPLType -> String -> Loc -> Error
expectedReturn fName expect got (Loc line col) = Error line col ("Expected function '" ++ fName ++ "' on Line " ++ show line ++ " and Col " ++ show col ++ " to return " ++ pp expect ++" but returned " ++ got)


-- ========== TI Errors ==========
refBeforeDec :: (LOC a, PrettyPrinter a) => String -> a -> Error
refBeforeDec s id = Error (getLineNum id) (getColNum id) (s++"'" ++ pp id ++ "', referenced " ++ showLoc id ++ ", has not been defined yet. (i.e. reference before declaration)")

doubleDef id = Error (getLineNum id) (getColNum id) ("Variable: " ++ showIDLoc id ++ ", already exists in the type environment. (i.e. double decleration)")

funcCallMoreArgs id = Error (getLineNum id) (getColNum id) ("Function: '" ++ pp id ++ "',  " ++ showLoc id ++ ", called with too many arguments.")
funcCallLessArgs id = Error (getLineNum id) (getColNum id) ("Function: '" ++ pp id ++ "',  " ++ showLoc id ++ ", called with too many arguments.")