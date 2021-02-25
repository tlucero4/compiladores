
module Optimizer (
   optimize
   ) where

import Lang
import MonadPCF
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy

apply2Term :: (Term -> Term) -> TDecl Term -> TDecl Term
apply2Term f (TDecl p n t b) = TDecl p n t $ f b

optimize :: MonadPCF m => [TDecl Term] -> m [TDecl Term]
optimize = optimizeCycle 1
                     
optimizeCycle :: MonadPCF m => Int -> [TDecl Term] -> m [TDecl Term]
optimizeCycle 0 ts = return ts
optimizeCycle n ts = do let ts' = map (apply2Term arithCalc) ts
                            ts'' = map (apply2Term commonSubExpr) ts'
                        ts''' <- inlineFun ts''
                        optimizeCycle (n-1) ts'''
                        

-- Reducing Arithmetic Expressions:

arithCalc :: Term -> Term
arithCalc (Lam i n ty t) = Lam i n ty (arithCalc t)
arithCalc (App i t u) = App i (arithCalc t) (arithCalc u)
arithCalc (Fix i f fty n nty t) = Fix i f fty n nty (arithCalc t)
arithCalc (IfZ i c t e) = IfZ i (arithCalc c) (arithCalc t) (arithCalc e)
arithCalc (Let i n ty d t) = Let i n ty (arithCalc d) (arithCalc t)
arithCalc (UnaryOp i o t) = UnaryOp i o (arithCalc t)
arithCalc (BinaryOp i o t u) = case (t, u) of
                                    (Const i (CNat n), Const _ (CNat m)) -> case o of
                                                                                 Add -> Const i (CNat $ n + m)
                                                                                 Sub -> Const i (CNat $ n - m) -- Arreglar resta n < m
                                                                                 Prod -> Const i (CNat $ n * m)
                                    otherwise                            -> BinaryOp i o (arithCalc t) (arithCalc u)
arithCalc t = t

-- Reducing Common Subexpressions:

commonSubExpr :: Term -> Term
commonSubExpr t = t -- Hacer

-- Creating In Line Functions:
                                          
calcSizeOfFun :: Term -> Int -- The Heuristic
calcSizeOfFun (Lam _ _ _ t) = 1 + calcSizeOfFun t
calcSizeOfFun (App _ t u) = 1 + calcSizeOfFun t + calcSizeOfFun u
calcSizeOfFun (Fix _ _ _ _ _ t) = 2 + calcSizeOfFun t
calcSizeOfFun (IfZ _ c t e) = calcSizeOfFun c + calcSizeOfFun t + calcSizeOfFun e
calcSizeOfFun (Let _ _ _ d t) = calcSizeOfFun d + calcSizeOfFun t
calcSizeOfFun (UnaryOp _ _ t) = calcSizeOfFun t
calcSizeOfFun (BinaryOp _ _ t u) = calcSizeOfFun t + calcSizeOfFun u
calcSizeOfFun t = 1

getFuns :: [TDecl Term] -> Writer [(Name, Term, Int)] ()
getFuns [] = return ()
getFuns (x:xs) = case (tdeclType x) of
                      FunTy _ _ -> do let s = calcSizeOfFun (tdeclBody x)
                                      tell [(tdeclName x, tdeclBody x, s)]
                                      getFuns xs  
                      _         -> getFuns xs

deleteFun :: Name -> [TDecl Term] -> [TDecl Term]
deleteFun _ [] = []
deleteFun n (x:xs) = if (n == tdeclName x) then xs
                                           else x : (deleteFun n xs)

substLam :: Term -> Term -> Term
substLam r (App i t u) = App i (substLam r t) (substLam r u)
substLam r (Lam i x ty t) = Lam i x ty (substLam r t)
substLam r (Fix i f fty x xty t) =Fix i f fty x xty (substLam r t)
substLam r (IfZ i c t e) = IfZ i (substLam r c) (substLam r t) (substLam r e)
substLam r (Let i x ty d t) = Let i x ty (substLam r d) (substLam r t)
substLam r (UnaryOp i o t) = UnaryOp i o (substLam r t)
substLam r (BinaryOp i o t u) = BinaryOp i o (substLam r t) (substLam r u)
substLam r (V i (Bound 0)) = r
substLam _ t = t

subst :: Term -> Term -> Term
subst term@(Fix i f fty x xty t) u = term
subst (Lam _ _ _ t) u = substLam t u

replaceFun :: Name -> Term -> Term -> Term
replaceFun n r (App i t u) = case t of
                                  V _ (Free n) -> subst r u
                                  _            -> App i (replaceFun n r t) (replaceFun n r u)
replaceFun n r (Lam i x ty t) = Lam i x ty (replaceFun n r t)
replaceFun n r (Fix i f fty x xty t) =Fix i f fty x xty (replaceFun n r t)
replaceFun n r (IfZ i c t e) = IfZ i (replaceFun n r c) (replaceFun n r t) (replaceFun n r e)
replaceFun n r (Let i x ty d t) = Let i x ty (replaceFun n r d) (replaceFun n r t)
replaceFun n r (UnaryOp i o t) = UnaryOp i o (replaceFun n r t)
replaceFun n r (BinaryOp i o t u) = BinaryOp i o (replaceFun n r t) (replaceFun n r u)
replaceFun _ _ t = t

doInline :: [TDecl Term] -> (Name, Term, Int) -> [TDecl Term]
doInline ts (n, t, i) = if i < 5 then map (apply2Term (replaceFun n t)) (deleteFun n ts)
                                 else ts
                      
inlineFun :: MonadPCF m => [TDecl Term] -> m [TDecl Term]
inlineFun ts = do let (_, table) = runWriter (getFuns ts)
                      ts' = foldl doInline ts table  
                  return ts'
                  
---------
