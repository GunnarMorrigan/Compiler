{-# LANGUAGE LambdaCase #-}
module MutRec where

import Data.Graph as Graph

import Data.Tree
-- import Data.Graph.SCC as SCC
import Parser
import AST
 
import System.Exit


class SPLGraph a where
    toGraph :: a -> [(Decl, IDLoc, [IDLoc])]

class Callees a where 
    getCallees :: a -> [IDLoc]

instance SPLGraph a => SPLGraph [a] where
    toGraph [] = []
    toGraph (x:xs) = toGraph x ++ toGraph xs

instance Callees a => Callees [a] where
    getCallees [] = []
    getCallees (x:xs) = getCallees x ++ getCallees xs

instance SPLGraph SPL where
    toGraph (SPL []) = []
    toGraph (SPL x) = toGraph x
 
instance SPLGraph Decl where
    toGraph (VarMain (VarDeclVar id e)) = [(VarMain  $ VarDeclVar id e, id, getCallees e)]
    toGraph (VarMain (VarDeclType t id e)) = [(VarMain $ VarDeclType t id e, id, getCallees e)]
    toGraph (FuncMain (FunDecl id args t d s)) = let fd = FunDecl id args t d s in [(FuncMain fd, id, getCallees fd)]

instance Callees Decl where
    getCallees (VarMain e) = getCallees e
    getCallees (FuncMain e) = getCallees e 

instance Callees FunDecl where
    getCallees (FunDecl _ _ _ vs stmts) = getCallees vs ++ getCallees stmts

instance Callees VarDecl where
    getCallees (VarDeclVar _ e) = getCallees e 
    getCallees (VarDeclType _ _ e) = getCallees e
    
instance Callees Stmt where
    getCallees (StmtIf e xs (Just ys)) = getCallees xs ++ getCallees ys
    getCallees (StmtIf e xs Nothing) = getCallees xs
    getCallees (StmtWhile e xs) = getCallees xs
    getCallees (StmtDeclareVar _ _ e) = getCallees e
    getCallees (StmtFuncCall (FunCall id e)) = id:getCallees e
    getCallees (StmtReturn (Just e)) = getCallees e
    getCallees (StmtReturn Nothing) = []

instance Callees Exp where
    getCallees (ExpFunCall (FunCall id e)) = id : getCallees e
    getCallees (ExpOp2 e1 op e2) = getCallees e1 ++ getCallees e2
    getCallees (ExpOp1 op e) = getCallees e
    getCallees (ExpBracket e) = getCallees e
    getCallees (ExpList e) = getCallees e
    getCallees (ExpTuple (e1, e2)) = getCallees e1 ++ getCallees e2
    getCallees (ExpId id fields) = [id]
    getCallees _ = []


mainMutRec :: String -> IO()
mainMutRec filename = do
       file <- readFile $ "../SPL_test_code/"++filename
       case tokeniseAndParse mainSegments file of
           Right (x,xs) -> print $ toGraph x
           Left x -> print x

mainMutRec1 :: String -> IO()
mainMutRec1 filename = do
       file <- readFile $ "../SPL_test_code/"++filename
       case tokeniseAndParse mainSegments file of
        --    Right (x,xs) -> let (g, v, f) = graphFromEdges $ toGraph x in print $ scc g
           Right (x,xs) -> putStr $ pp $ fromGraph $ stronglyConnCompR $ toGraph x
           Left x -> print x


mainMutRec2 :: String -> IO()
mainMutRec2 filename = do
       file <- readFile $ splFilePath++filename
       case tokeniseAndParse mainSegments file of 
              Right (x, _) -> do
                    writeFile "../SPL_test_code/out.spl" $ pp $ fromGraph $ stronglyConnCompR $ toGraph x
              Left x -> do
                    print x
                    exitFailure

showSCC :: [SCC (Decl, String, [String])] -> IO()
-- showSCC ((AcyclicSCC x):xs) = do
--     print (AcyclicSCC x)
--     showSCC xs
showSCC [x] = print x
showSCC (x:xs) = do
    print x
    showSCC xs

getCyclics :: [SCC (Decl, String, [String])] -> [SCC (Decl, String, [String])]
getCyclics ((CyclicSCC x):xs) = CyclicSCC x : getCyclics xs
getCyclics (_:xs) = getCyclics xs
getCyclics [] = []

-- TODO CyclicSCC can also container VarDecls and should then throw and error
-- because variables cant be Cyclic
-- var hoi = hoi2;
-- var hoi2 = hoi;
fromGraph :: [SCC (Decl, IDLoc, [IDLoc])]  -> SPL
fromGraph x = SPL (f x)
    where 
        f [] = []
        f ((AcyclicSCC (x,_,_)):xs)  = x : f xs
        f ((CyclicSCC ys):xs)  = MutRec (map (\(FuncMain f,_,_) -> f) ys) : f xs
        
-- castCyclicToMutRec :: SCC (Decl, String, [String]) -> Decl
-- castCyclicToMutRec (CyclicSCC ys):xs)