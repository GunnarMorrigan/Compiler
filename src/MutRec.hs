module MutRec where

import Data.Graph as Graph

import Data.Tree
-- import Data.Graph.SCC as SCC
import Parser
import AST
 
class SPLGraph a where
    toGraph :: a -> [(Decl, String, [String])]
    fromGraph :: [(Decl, String, [String])] -> a
    getCallees :: a -> [ID]

instance SPLGraph a => SPLGraph [a] where
    toGraph [] = []
    toGraph (x:xs) = toGraph x ++ toGraph xs
    getCallees [] = []
    getCallees (x:xs) = getCallees x ++ getCallees xs
    

instance SPLGraph SPL where
    toGraph (SPL []) = []
    toGraph (SPL x) = toGraph x
 
instance SPLGraph Decl where
    toGraph (VarMain (VarDeclVar id e)) = [(VarMain  $ VarDeclVar id e, id, getCallees e)]
    toGraph (VarMain (VarDeclType t id e)) = [(VarMain $ VarDeclType t id e, id, getCallees e)]
    toGraph (FuncMain (FunDecl id args t d s)) = let fd = FunDecl id args t d s in [(FuncMain fd, id, getCallees fd)]
    getCallees (VarMain e) = getCallees e
    getCallees (FuncMain e) = getCallees e 

instance SPLGraph FunDecl where
    getCallees (FunDecl _ _ _ vs stmts) = getCallees vs ++ getCallees stmts

instance SPLGraph VarDecl where
    getCallees (VarDeclVar _ e) = getCallees e 
    getCallees (VarDeclType _ _ e) = getCallees e
    
instance SPLGraph Stmt where
    getCallees (StmtIf e xs (Just ys)) = getCallees xs ++ getCallees ys
    getCallees (StmtIf e xs Nothing) = getCallees xs
    getCallees (StmtWhile e xs) = getCallees xs
    getCallees (StmtDeclareVar _ _ e) = getCallees e
    getCallees (StmtFuncCall (FunCall id e)) = id:getCallees e
    getCallees (StmtReturn (Just e)) = getCallees e
    getCallees (StmtReturn Nothing) = []

instance SPLGraph Exp where
    getCallees (ExpFunCall (FunCall id e)) = id : getCallees e
    getCallees (ExpOp2 e1 op e2) = getCallees e1 ++ getCallees e2
    getCallees (ExpOp1 op e) = getCallees e
    getCallees (ExpBracket e) = getCallees e
    getCallees (ExpList e) = getCallees e
    getCallees (ExpTuple (e1, e2)) = getCallees e1 ++ getCallees e2
    getCallees _ = []


mainMutRec :: String -> IO()
mainMutRec filename = do
       file <- readFile $ "../SPL_code/"++filename
       case tokeniseAndParse mainSegments file of
           Right (x,xs) -> print $ toGraph x
           Left x -> print x

mainMutRec1 :: String -> IO()
mainMutRec1 filename = do
       file <- readFile $ "../SPL_code/"++filename
       case tokeniseAndParse mainSegments file of
        --    Right (x,xs) -> let (g, v, f) = graphFromEdges $ toGraph x in print $ scc g
           Right (x,xs) -> showSCC $ stronglyConnCompR $ toGraph x
           Left x -> print x

showSCC :: [SCC] -> IO()
showSCC ((AcyclicSCC x):xs) = print (AcyclicSCC x)
showSCC ((CyclicSCC x):xs) = do
    putStr "\n\n"
    print ys

 --graphFromEdges :: Ord key => [(node, key, [key])] -> (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)