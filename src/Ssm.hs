module Ssm where

import Prelude hiding ( EQ, LT, GT )

newtype SSM =  SSM [Idecl] 
  deriving (Show, Eq)

data Idecl = 
    SSMGlobal [Instruct] |
    SSMFunction String [Instruct]
    -- Function String [Instruct] String [Instruct]
    deriving (Show, Eq)

data Instruct = 
    LDAL String | -- Load address of label to make high order functions possible. 
    LABEL Instruct | -- this instruction has a label in front of the actual instruction.
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
