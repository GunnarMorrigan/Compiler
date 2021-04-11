{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
module Error where

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

data Loc = Loc Int Int
    deriving (Eq, Show)

defaultLoc :: Loc
defaultLoc = Loc (-1) (-1)