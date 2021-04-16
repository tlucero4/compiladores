
module Optimizer (
   optimize
   ) where

import Lang
import Common (Pos(NoPos))
import MonadPCF
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy

apply2Term :: (Term -> Term) -> TDecl Term -> TDecl Term
apply2Term f (TDecl p n t b) = TDecl p n t $ f b

optimize :: MonadPCF m => [TDecl Term] -> m [TDecl Term]
optimize = optimizeCycle 2
                     
optimizeCycle :: MonadPCF m => Int -> [TDecl Term] -> m [TDecl Term]
optimizeCycle 0 ts = return ts
optimizeCycle n ts = do let ts' = map (apply2Term arithCalc) ts
                            ts'' = map (apply2Term commonSubExpr) ts'
                        ts''' <- inlineFun ts''
                        optimizeCycle (n-1) ts'''
                        

-- Reducing Arithmetic Expressions (and Dead Code Elimination):

arithCalc :: Term -> Term
arithCalc (Lam i n ty t) = Lam i n ty (arithCalc t)
arithCalc (App i t u) = App i (arithCalc t) (arithCalc u)
arithCalc (Fix i f fty n nty t) = Fix i f fty n nty (arithCalc t)
arithCalc (IfZ i c t e) = case c of -- DCE
                               Const _ (CNat 0) -> (arithCalc t)
                               Const _ (CNat n) -> (arithCalc e)
                               _ -> IfZ i (arithCalc c) (arithCalc t) (arithCalc e)
arithCalc (Let i n ty d t) = Let i n ty (arithCalc d) (arithCalc t)
arithCalc (UnaryOp i o t) = UnaryOp i o (arithCalc t)
arithCalc (BinaryOp i o t u) = let t' = arithCalc t
                                   u' = arithCalc u
                               in case (t', u') of
                                    (Const i (CNat n), Const _ (CNat m)) -> case o of
                                                                                 Add -> Const i (CNat $ n + m)
                                                                                 Sub -> if (n > m) then Const i (CNat $ n - m) else Const i (CNat 0)
                                                                                 Prod -> if (n == 0 || m == 0) then Const i (CNat 0) else Const i (CNat $ n * m)
                                    _                                    -> BinaryOp i o t' u'
arithCalc t = t

-- Reducing Common Subexpressions:

commonSubExpr :: Term -> Term
commonSubExpr t = t -- Hacer

-- Creating In Line Functions:

getFreshName :: State Int Name
getFreshName = do i <- get
                  modify (+1)
                  return ("__nv" ++ show i)
                                          
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

deleteFun :: Name -> [TDecl Term] -> [TDecl Term] -- Por ahora no la usamos
deleteFun _ [] = []
deleteFun n (x:xs) = if (n == tdeclName x) then xs
                                           else x : (deleteFun n xs)

substLam :: Term -> Int -> Term -> Term
substLam r k (App i t u) = App i (substLam r k t) (substLam r k u)
substLam r k (Lam i x ty t) = substLam r k t
substLam r k (Fix i f fty x xty t) = Fix i f fty x xty (substLam r k t)
substLam r k (IfZ i c t e) = IfZ i (substLam r k c) (substLam r k t) (substLam r k e)
substLam r k (Let i x ty d t) = Let i x ty (substLam r k d) (substLam r k t)
substLam r k (UnaryOp i o t) = UnaryOp i o (substLam r k t)
substLam r k (BinaryOp i o t u) = BinaryOp i o (substLam r k t) (substLam r k u)
substLam r k t@(V i (Bound n)) = if (n == k) then r else t
substLam _ _ t = t

substLamR :: Int -> [Term] ->  Term -> State Int Term
substLamR k [] t = return t
substLamR k (x:xs) t = case x of
                            V _ _ -> substLamR (k+1) xs (substLam x k t)
                            Const _ _ -> substLamR (k+1) xs (substLam x k t)
                            t' ->  do fr <- getFreshName
                                      substLamR (k+1) xs (Let NoPos fr NatTy x $ substLam (V NoPos (Bound 0)) k t)


replaceApp :: Term -> Name -> [Term] -> Maybe [Term]
replaceApp (App i t a) n as = replaceApp t n (a:as)
replaceApp (V _ (Free n')) n as = if (n == n') then Just as
                                               else Nothing
replaceApp _ _ _ = Nothing

replaceFun :: Name -> Term -> Term -> Term
replaceFun n r x@(App i t a) = case (replaceApp t n [a]) of
                                  Just as -> case r of
                                                  Lam _ _ _ t' -> let (ft, _) = runState (substLamR 0 (reverse as) t') 0
                                                                  in ft
                                                  Fix _ _ _ _ _ t' -> undefined
                                                  _ -> undefined
                                  Nothing -> App i (replaceFun n r t) (replaceFun n r a)
replaceFun n r (Lam i x ty t) = Lam i x ty (replaceFun n r t)
replaceFun n r (Fix i f fty x xty t) = Fix i f fty x xty (replaceFun n r t)
replaceFun n r (IfZ i c t e) = IfZ i (replaceFun n r c) (replaceFun n r t) (replaceFun n r e)
replaceFun n r (Let i x ty d t) = Let i x ty (replaceFun n r d) (replaceFun n r t)
replaceFun n r (UnaryOp i o t) = UnaryOp i o (replaceFun n r t)
replaceFun n r (BinaryOp i o t u) = BinaryOp i o (replaceFun n r t) (replaceFun n r u)
replaceFun _ _ t = t

doInline :: [TDecl Term] -> (Name, Term, Int) -> [TDecl Term]
doInline ts (n, t, i) = if i < 12 then map (apply2Term (replaceFun n t)) ts
                                  else ts
                      
inlineFun :: MonadPCF m => [TDecl Term] -> m [TDecl Term]
inlineFun ts = do let (_, table) = runWriter (getFuns ts)
                      ts' = foldl doInline ts table  
                  return ts'
                  
---------
