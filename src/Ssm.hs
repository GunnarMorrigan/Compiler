module Ssm where
    
import AST

import Prelude hiding ( EQ, LT, GT )
import Data.List ( intercalate )

data SSM =  SSM [SsmGlobal] [SsmFunction]
  deriving (Show, Eq)

data Idecl = 
    SsmGlobal SsmGlobal |
    SsmFunction SsmFunction
    -- Function String [Instruct] String [Instruct]
    deriving (Show, Eq)

newtype SsmGlobal = Global [Instruct]
    deriving (Show, Eq)

data SsmFunction = Function String [Instruct]
    deriving (Show, Eq)

data Instruct = 
    LDAL String | -- Load address of label to make high order functions possible. 
    LABEL String Instruct | -- this instruction has a label in front of the actual instruction.
    COMMENT Instruct String | -- this instruction contains a comment
    LDC Int |
    LDS Int |
    LDMS Int |
    STS Int |
    STMS Int Int |
    LDSA Int |
    LDL Int |
    LDML Int Int |
    STL Int |
    STML Int Int |
    LDLA Int |
    LDA Int |
    -- LDMA |
    LDAA Int |
    STA Int |
    -- STMA |
    LDR Register |
    LDRR Register Register |
    STR Register |
    SWP |
    SWPR Register |
    SWPRR Register Register |
    AJS Int |
    ADD |
    MUL |
    SUB |
    DIV |
    MOD |
    AND |
    OR |
    XOR |
    EQ |
    NE |
    LT |
    LE |
    GT |
    GE |
    NEG |
    NOT |
    BSR String |
    BRA String |
    BRF String |
    BRT String |
    JSR |
    RET |
    LINK Int |
    UNLINK |
    NOP |
    HALT |
    TRAP Int |
    -- ANNOTE |
    LDH Int |
    -- LDMH |
    -- STH |
    STMH Int
    deriving (Show, Eq)

data Register = 
    PC | SP | MP | HP | RR |
    R5 | R6 | R7
    deriving (Show, Eq)

nullary = [SWP, ADD, MUL, SUB, DIV, MOD, AND, OR, XOR, EQ, NE, LT, LE, GT, NEG, NOT, JSR, RET, UNLINK, NOP, HALT]
unary = undefined 

size :: Instruct -> Int
size a | a `elem` nullary = 1
size (SWPRR _ _) = 3
-- size (LDMH _ _) = 3
size (LDRR _ _) = 3
-- size (STMA _ _) = 3
-- size (LDMA _ _) = 3
size (STML _ _) = 3
size (LDML _ _) = 3
size (STMS _ _) = 3
size _ = 2



instance PrettyPrinter SSM where
   pp (SSM globals functions) = 
       if null globals  
            then pp functions
            else 
                pp [LDSA 1,STR R5] ++ "\n" ++ pp globals ++"\n" ++ 
                pp (BRA "main")++ "\n" ++  
                pp functions

instance PrettyPrinter SsmGlobal where
   pp (Global inst) = pp inst
       
instance PrettyPrinter SsmFunction where
   pp (Function s (i:is)) = intercalate "\n" $ pp i : map (('\t':) . pp) is

instance PrettyPrinter Instruct where
    pp (LDAL s) = undefined

    pp ADD = "ADD"
    pp MUL = "MUL"
    pp SUB = "SUB"
    pp DIV = "DIV"
    pp MOD = "MOD"
    pp AND = "AND"
    pp OR = "OR"
    pp XOR = "XOR"
    pp EQ = "EQ"
    pp NE = "NE"
    pp LT = "LT"
    pp LE = "LE"
    pp GT = "GT"
    pp GE = "GE"
    pp NEG = "NEG"
    pp NOT = "NOT"
    pp JSR = "JSR"
    pp SWP = "SWP"
    pp RET = "RET"
    pp NOP = "NOP"
    pp HALT = "HALT"
    pp UNLINK = "UNLINK"


    pp (LABEL s instruct) = s ++ ":  " ++ pp instruct
    pp (COMMENT instruct s) = pp instruct ++ " //" ++ s
    pp (LDC i) = "LDC " ++ show i
    pp (LDS i) = "LDS " ++ show i
    pp (LDMS i) = "LDMS " ++ show i
    pp (STS i) = "STS " ++ show i
    pp (LDSA i) = "LDSA " ++ show i
    pp (LDL i) = "LDL " ++ show i
    pp (STL i) = "STL " ++ show i
    pp (LDLA i) = "LDLA " ++ show i
    pp (LDA i) = "LDA " ++ show i
    pp (LDAA i) = "LDAA " ++ show i
    pp (STA i) = "STA " ++ show i
    pp (LDR r) = "LDR " ++ show r
    pp (STR r) = "STR " ++ show r
    pp (SWPR r) = "SWPR " ++ show r

    pp (BSR s) = "BSR " ++ s
    pp (BRA s) = "BRA " ++ s
    pp (BRF s) = "BRF " ++ s
    pp (BRT s) = "BRT " ++ s
    pp (AJS i) = "AJS " ++ show i
    pp (LINK i) = "LINK " ++ show i
    pp (TRAP i) = "TRAP " ++ show i
    pp (LDH i) = "LDH " ++ show i
    pp (STMH i) = "STMH " ++ show i

    pp (STMS i1 i2) = "STMS " ++ show i1 ++ show i2
    pp (LDML i1 i2) = "LDML " ++ show i1 ++ show i2
    pp (STML i1 i2) = "STML " ++ show i1 ++ show i2
    pp (LDRR r1 r2) = "LDRR " ++ show r1 ++ show r2
    pp (SWPRR r1 r2) = "SWPRR " ++ show r1 ++ show r2

    -- pp (LDMA) = undefined
    -- pp (STMA) = undefined
    -- pp (ANNOTE) = undefined
    -- pp (LDMH) = undefined
    -- pp (STH) = undefined


