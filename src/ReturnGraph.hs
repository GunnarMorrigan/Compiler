module ReturnGraph where

import Lexer
import AST

class ReturnGraph a where
    returnGraph :: a -> Either Error (a,SPLType)

instance ReturnGraph a => ReturnGraph [a] where
    returnGraph (x:xs) = do
        (first, t) <- returnGraph x
        (sec, t') <- returnGraph xs

        return $ if t==t' then (first:sec) else Left Error (-1) (-1) "Function has different (implicit) return types"


instance ReturnGraph SPL where
    returnGraph (SPL xs) = SPL <$> returnGraph xs

instance ReturnGraph Decl where
    returnGraph (FuncMain x) = do
        l <- returnGraph x
        return $ FuncMain l
    returnGraph (MutRec []) = undefined
    returnGraph (MutRec (x:xs)) = undefined
    returnGraph x = Right (x,x) 

instance ReturnGraph FunDecl where
    returnGraph (FunDecl _ _ _ _ xs) = lala xs



findType :: [Stmt] -> Maybe Bool -> Either Error Bool 
findType [] Nothing = Right False 
findType (x:xs) foundReturn = case x of
    StmtIf _ stmts Nothing -> undefined
    StmtIf _ stmts (Just e) -> undefined
    StmtWhile _ stmts -> undefined
    StmtDeclareVar {} -> findType xs
    StmtFuncCall  {} -> findType xs
    StmtReturn (Just e) -> Right True
    StmtReturn Nothing -> Right False


-- instance ReturnGraph Stmt where
--     returnGraph (StmtIf e stmts ) 



