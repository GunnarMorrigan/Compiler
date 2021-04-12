{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
module Error where

import AST

import Data.List
import Data.Char
import Control.Applicative

data Error = Error Int Int String
  deriving (Show)

instance Eq Error where
  (==) (Error line col m) (Error line' col' m') =  line == line' && col == col'

instance Ord Error where
  (Error line col m) `compare` (Error line' col' m') = if line == line' then compare col col' else compare line line'

-- instance Show Error where
--   show (Error (-1) (-1) message) = message
--   show (Error line col message) = message ++ ", on line: " ++show line ++ " and character: " ++ show col 

instance Alternative (Either Error) where
  empty = Left $ Error 0 0 ""
  Left x <|> Left y = Left $ max x y
  Left _ <|> e2 = e2
  e1 <|> _ = e1

showPlaceOfError :: String -> Error -> String
showPlaceOfError code (Error line col msg) =
    dropWhile isSpace $ lines code !! (line -1) ++ "\n"
    ++ replicate (col-1) ' ' ++ "^\n"

defaultLoc :: Loc
defaultLoc = Loc (-1) (-1)


refBeforeDec :: (LOC a, PrettyPrinter a) => String -> a -> Error
refBeforeDec s id = Error (getLineNum id) (getColNum id) (s++"'" ++ pp id ++ "', referenced " ++ showLoc id ++ ", has not been defined yet: (i.e. reference before declaration)")

doubleDef id = Error (getLineNum id) (getColNum id) ("Variable with name: '" ++ showIDLoc id ++ "', already exists in the type environment: (i.e. double decleration)")

funcCallMoreArgs id = Error (getLineNum id) (getColNum id) ("Function: '" ++ pp id ++ "',  " ++ showLoc id ++ ", called with too many arguments.")
funcCallLessArgs id = Error (getLineNum id) (getColNum id) ("Function: '" ++ pp id ++ "',  " ++ showLoc id ++ ", called with too many arguments.")