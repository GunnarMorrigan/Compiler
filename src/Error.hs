{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
module Error where

import AST

import Data.List
import Data.Char

import Control.Applicative

data Error = 
  Error Loc String|
  ErrorD ErrorLoc String|
  Errors [Error]
  deriving (Show)


instance LOC Error where
  showLoc (Error loc _) = showLoc loc
  showLoc (ErrorD dloc _ ) = showLoc dloc
  
  getDLoc (Error loc _) = undefined
  getDLoc (ErrorD dloc _) = dloc

  getFstLoc (Error loc _) = loc
  getFstLoc (ErrorD dloc _) = getFstLoc dloc
  getFstLoc (Errors (x:xs)) = getFstLoc x

  getSndLoc (Error loc _) = undefined 
  getSndLoc (ErrorD dloc _) = getSndLoc dloc 

  getLineNum (Error loc _) = getLineNum loc
  getLineNum (ErrorD dloc _) = getLineNum dloc

  getColNum (Error loc _) = getColNum loc
  getColNum (ErrorD dloc _) = getColNum dloc



instance Semigroup Error where
  (<>) (Error loc s) (Error loc' s') = Errors [Error loc s,Error loc' s']
  (<>) (ErrorD loc s) (ErrorD loc' s') = Errors [ErrorD loc s,ErrorD loc' s']

  (<>) (Error loc s) (ErrorD loc' s') = Errors [Error loc s,ErrorD loc' s']
  (<>) (ErrorD loc s) (Error loc' s') = Errors [ErrorD loc s,Error loc' s']

  (<>) (Errors errs) (Error loc s) = Errors $ errs ++ [Error loc s]
  (<>) (Error loc s) (Errors errs)   = Errors $ Error loc s:errs
  (<>) (Errors errs) (ErrorD loc s) = Errors $ errs ++ [ErrorD loc s]
  (<>) (ErrorD loc s) (Errors errs)   = Errors $ ErrorD loc s:errs

  (<>) (Errors errs) (Errors errs')  = Errors $ errs ++ errs'

instance Eq Error where
  (==) (Error a m) (Error b m') = a == b
  (==) (ErrorD a m) (ErrorD b m') = a == b
  (==) (Errors a) (Errors b) = a == b


instance Ord Error where
  (Error (Loc line col) m) `compare` (Error (Loc line' col') m') = if line == line' then  col `compare` col' else line `compare` line'
  (ErrorD (DLoc (Loc line col) _ ) m) `compare` (Error (Loc line' col') m') = if line == line' then  col `compare` col' else line `compare` line'
  (Error (Loc line col) m) `compare` (ErrorD (DLoc (Loc line' col') _ ) m') = if line == line' then  col `compare` col' else line `compare` line'
  (ErrorD (DLoc (Loc line col) _ ) m) `compare` (ErrorD (DLoc (Loc line' col') _ ) m') = if line == line' then  col `compare` col' else line `compare` line'

-- instance Show Error where
  -- show (Error _ message) = message
  -- show (ErrorD _ message) = message
  -- show (Errors errs) = intercalate "\n" (map show errs)

instance Alternative (Either Error) where
  empty = Left $ Error (Loc 0 0) ""
  Left x <|> Left y = Left $ max x y
  Left _ <|> e2 = e2
  e1 <|> _ = e1

showError :: String -> Error -> String
showError code (Error loc s) = showPlaceOfError code (Error loc s)
showError code (ErrorD loc s) = showPlaceOfError code (ErrorD loc s)
showError code (Errors errs) = showPlacesOfErrors code errs

showPlacesOfErrors :: String -> [Error] -> String
showPlacesOfErrors code' errs = intercalate "\n" $ map (showPlaceOfError code') errs

showPlaceOfError :: String -> Error -> String
showPlaceOfError code' (Error (Loc (-1) (-1)) msg) = msg ++ "\n"
showPlaceOfError code' (ErrorD (DLoc (Loc (-1) (-1)) (Loc (-1) (-1))) msg) = msg ++ "\n"
showPlaceOfError code' (Error (Loc line col) msg) =
    let code = replaceTab code' in
    msg ++ "\n" ++
    (if line == 1 then "" else lines code !! (line - 2) ++ "\n" )
    ++ makePlaceOfErrorRed (col-1) col (lines code !! (line - 1)) ++ "\n"
    ++ replicate (if col > 2 then col-2 else 0) ' ' ++ "^\n"
    ++ if length code > line then lines code !! line ++ "\n" else ""
showPlaceOfError code' (ErrorD (DLoc (Loc line col) (Loc line' col')) msg) =
    let code = replaceTab code' in
    msg ++ "\n" ++
    (if line == 1 then "" else lines code !! (line - 2) ++ "\n" )
    ++ makePlaceOfErrorRed (col-1) (col'-1) ( lines code !! (line - 1)) ++ "\n"
    ++ replicate (col - 1) ' ' ++ replicate (col'-col) '^' ++ "\n"
    ++ if length code > line then lines code !! line ++ "\n" else "" 
showPlaceOfError code' x = show x

makePlaceOfErrorRed :: Int -> Int -> String -> String
makePlaceOfErrorRed ca cb s = do
  let (l,r) = splitAt ca s
  let (r1,r2) = splitAt (cb-ca) r
  l ++ red ++ r1 ++ reset ++ r2


replaceTab :: String -> String
replaceTab [] = []
replaceTab (x:xs) | x== '\t' = "    " ++ replaceTab xs
replaceTab (x:xs)  = x:replaceTab xs

defaultLoc :: Loc
defaultLoc = Loc (-1) (-1)

defaultErrorLoc :: ErrorLoc
defaultErrorLoc = DLoc defaultLoc defaultLoc

-- ========== Parser Errors ==========
missingSeparator loc sepToken token = ErrorD loc ("Expected separator '"++ show sepToken ++ "' but found '" ++ show token ++ "' on " ++ showLoc loc)
unexpectedToken expected found loc = ErrorD loc ("Expected: '"++show expected++"' but found: '" ++ show found ++ "' on " ++ showLoc loc)
unexpectedEOF expected = Error defaultLoc ("Unexpected EOF, expected: "++show expected++".")
trueUnexpectedEOF = Error defaultLoc "Unexpected EOF." 

-- ========== ReturnGraph Errors ==========
missingReturn :: String -> SPLType -> Loc -> Error
missingReturn fName t loc = Error loc ("Missing return statement in function '" ++ fName ++ "' on " ++ showLoc loc ++ ", expected return statement of type " ++ pp t ++ " but got no return, please add a return statement to the function")  
conflictingReturn :: String -> Loc -> Error 
conflictingReturn fName loc = Error loc ("Found conflicting return types on " ++ showLoc loc ++", types Void and non Void for function '" ++ fName ++ "'") 
expectedReturn :: String -> SPLType -> String -> Loc -> Error
expectedReturn fName expect got loc = Error loc ("Expected function '" ++ fName ++ "' on " ++ showLoc loc ++ " to return " ++ pp expect ++" but returned " ++ got)

-- ========== TI Errors ==========
refBeforeDec :: (LOC a, PrettyPrinter a) => String -> a -> Error
refBeforeDec s id = ErrorD (getDLoc id) (s++"'" ++ pp id ++ "', referenced " ++ showLoc id ++ ", has not been defined yet. (i.e. reference before declaration)")

assigningToStdFunction id = ErrorD (getDLoc id) "Assigning to standard library function."
declaringStdFunction id = ErrorD (getDLoc id) "Attempting to overwrite standard library function."

doubleDef id = ErrorD (getDLoc id) ("Variable: " ++ showIDLoc id ++ ", already exists in the type environment. (i.e. double decleration)")
doubleDef2 ida idb = Errors [erra,errb]
  where erra = ErrorD (getDLoc ida) ("Double declaration, id '" ++ pp ida ++ "' used multiple times: " ++ showLoc ida)
        errb = ErrorD (getDLoc idb) ("Double declaration, id '" ++ pp idb ++ "' used multiple times: " ++ showLoc idb)

stupidError m = Error defaultLoc (m++"\n")

funcCallMoreArgs id = ErrorD (getDLoc id) ("Function: '" ++ pp id ++ "',  " ++ showLoc id ++ ", called with too many arguments.")
funcCallLessArgs id = ErrorD (getDLoc id) ("Function: '" ++ pp id ++ "',  " ++ showLoc id ++ ", called with too few arguments.")

applVarAsFunc id = ErrorD (getDLoc id) ("Variable: '" ++ pp id ++ "', is being used as a function  " ++ showLoc id)

overloadedAsArgument id = ErrorD (getDLoc id) ("Function: '" ++ pp id ++ "', uses unclear overloading. \nUsing this as a higher order function is not allowed. \nProviding more rigid type signature may help.")

-- ========== Colors ==========
reset = "\x1b[0m"
bright = "\x1b[1m"
dim = "\x1b[2m"
underscore = "\x1b[4m"
blink = "\x1b[5m"
-- reverse = "\x1b[7m"
hidden = "\x1b[8m"

black = "\x1b[30m"
red = "\x1b[31m"
green = "\x1b[32m"
yellow = "\x1b[33m"
blue = "\x1b[34m"
magenta = "\x1b[35m"
cyan = "\x1b[36m"
white = "\x1b[37m"

-- BGblack = "\x1b[40m"
-- BGred = "\x1b[41m"
-- BGgreen = "\x1b[42m"
-- BGyellow = "\x1b[43m"
-- BGblue = "\x1b[44m"
-- BGmagenta = "\x1b[45m"
-- BGcyan = "\x1b[46m"
-- BGwhite = "\x1b[47m"