
module Optimizer (
   optimize
   ) where

import Lang
import Common (Pos(NoPos))
import Subst (closeN, substN)
import MonadPCF
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy

numCycles :: Int
numCycles = 1

inlineHeur :: Int
inlineHeur = 12

apply2Term :: (Term -> Term) -> TDecl Term -> TDecl Term
apply2Term f (TDecl p n t b) = TDecl p n t $ f b

optimize :: [TDecl Term] -> [TDecl Term]
optimize = optimizeCycle numCycles
                     
optimizeCycle :: Int -> [TDecl Term] -> [TDecl Term]
optimizeCycle 0 ts = ts
optimizeCycle n ts = let ts' = map (apply2Term arithCalc) ts
                         ts'' = inlineFun ts'
                     in optimizeCycle (n-1) ts''
                        

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
                  return ("nv" ++ show i)
                                          
calcSizeOfFun :: Term -> Int -- The Heuristic
calcSizeOfFun (Lam _ _ _ t) = 1 + calcSizeOfFun t
calcSizeOfFun (App _ t u) = 1 + calcSizeOfFun t + calcSizeOfFun u
calcSizeOfFun (Fix _ _ _ _ _ t) = 2 + calcSizeOfFun t
calcSizeOfFun (IfZ _ c t e) = calcSizeOfFun c + calcSizeOfFun t + calcSizeOfFun e
calcSizeOfFun (Let _ _ _ d t) = calcSizeOfFun d + calcSizeOfFun t
calcSizeOfFun (UnaryOp _ _ t) = calcSizeOfFun t
calcSizeOfFun (BinaryOp _ _ t u) = calcSizeOfFun t + calcSizeOfFun u
calcSizeOfFun t = 1

calcSizeOfArgs :: Ty -> Int
calcSizeOfArgs (FunTy _ t) = 1 + calcSizeOfArgs t
calcSizeOfArgs _ = 1

getFuns :: [TDecl Term] -> Writer [(Name, Term, Int, Int)] ()
getFuns [] = return ()
getFuns (x:xs) = case (tdeclType x) of
                      FunTy _ t -> do let s = calcSizeOfFun (tdeclBody x)
                                          nargs = calcSizeOfArgs t
                                      tell [(tdeclName x, tdeclBody x, s, nargs)]
                                      getFuns xs  
                      _         -> getFuns xs

deleteFun :: Name -> [TDecl Term] -> [TDecl Term] -- Por ahora no la usamos
deleteFun _ [] = []
deleteFun n (x:xs) = if (n == tdeclName x) then xs
                                           else x : (deleteFun n xs)

substLam :: Term -> Int -> Term -> Term
substLam r k (App i t u) = App i (substLam r k t) (substLam r k u)
substLam r k (Lam i x ty t) = Lam i x ty t
substLam r k (Fix i f fty x xty t) = Fix i f fty x xty t
substLam r k (IfZ i c t e) = IfZ i (substLam r k c) (substLam r k t) (substLam r k e)
substLam r k (Let i x ty d t) = Let i x ty (substLam r k d) (substLam r (k+1) t)
substLam r k (UnaryOp i o t) = UnaryOp i o (substLam r k t)
substLam r k (BinaryOp i o t u) = BinaryOp i o (substLam r k t) (substLam r k u)
substLam r k t@(V i (Bound n)) = if (n == k) then r else t
substLam _ _ t = t

substLamR :: Int -> [Name] -> [Term] ->  Term -> State Int Term
substLamR k ns [] t = return $ closeN (reverse ns) t -- k descuenta los argumentos totales y ns acumula los nombres de los args complejos
substLamR k ns (x:xs) (Lam _ _ _ t) = case x of
                                        V _ _ -> substLamR (k-1) ns xs $ substLam x k t
                                        Const _ _ -> substLamR (k-1) ns xs $ substLam x k t
                                        _ ->  do fr <- getFreshName
                                                 let it = substLam (V NoPos (Free fr)) k t
                                                 ap <- substLamR (k-1) (fr:ns) xs it
                                                 return (Let NoPos fr NatTy x ap)
substLamR _ _ _ _ = undefined

delAppFix :: Int -> Term -> Maybe Term
delAppFix k t@(App _ (V _ (Bound k')) u) = if (k + 1 == k') then Just t else Nothing
delAppFix k (App _ t u) = delAppFix k t
delAppFix _ _ = Nothing

substFix :: [Term] -> Int -> Term -> Term
substFix r k (App i t u) = case delAppFix k t of
                                Just a -> substFix r k a
                                Nothing -> App i (substFix r k t) (substFix r k u)
substFix r k (Lam i x ty t) = Lam i x ty t
substFix r k (Fix i f fty x xty t) = Fix i f fty x xty t
substFix r k (IfZ i c t e) = IfZ i (substFix r k c) (substFix r k t) (substFix r k e)
substFix r k (Let i x ty d t) = Let i x ty (substFix r k d) (substFix r k t)
substFix r k (UnaryOp i o t) = UnaryOp i o (substFix r k t)
substFix r k (BinaryOp i o t u) = BinaryOp i o (substFix r k t) (substFix r k u)
substFix r k (V i (Bound n)) = if (n < k) then (r !! n) else (V i (Bound (n-k)))
substFix _ _ t = t

upbound :: Int -> Term -> Term
upbound k (App i t u) = App i (upbound k t) (upbound k u)
upbound k (Lam i x ty t) = Lam i x ty (upbound k t)
upbound k (Fix i f fty x xty t) = Fix i f fty x xty (upbound k t)
upbound k (IfZ i c t e) = IfZ i (upbound k c) (upbound k t) (upbound k e)
upbound k (Let i x ty d t) = Let i x ty (upbound k d) (upbound k t)
upbound k (UnaryOp i o t) = UnaryOp i o (upbound k t)
upbound k (BinaryOp i o t u) = BinaryOp i o (upbound k t) (upbound k u)
upbound k (V i (Bound n)) = V i (Bound (n+k))
upbound _ t = t

substFixR :: Int -> [Term] -> Name -> Name -> Term -> Term
substFixR k as f n (Lam _ _ _ t) = substFixR (k+1) as f n t
substFixR k as f n t = let f' = f++"'"
                           n' = n++"'"
                           t' = substFix (map (upbound 2) $ reverse $ tail as) k t
                           letT = Fix NoPos f' NatTy n' NatTy t'
                           inT = App NoPos (V NoPos (Bound 0)) (upbound 1 $ head as)
                       in Let NoPos f' NatTy letT inT
                                      
getArgs :: Term -> Name -> [Term] -> Maybe [Term]
getArgs (App _ t a) n as = getArgs t n (a:as)
getArgs (V _ (Free n')) n as = if (n == n') then Just as
                                            else Nothing
getArgs _ _ _ = Nothing

replaceFun :: Name -> Term -> Int -> Term -> Term
replaceFun n r na x@(App i t a) = case (getArgs t n [a]) of
                                  Just as -> if length as == na then -- solo aceptamos optimizar funciones aplicadas totalmente
                                                case r of
                                                  Lam _ _ _ _ -> fst $ runState (substLamR (na - 1) [] as r) 0
                                                  Fix p f fty n nty t -> substFixR 0 as f n t 
                                                  _ -> App i (replaceFun n r na t) (replaceFun n r na a)
                                                                else App i (replaceFun n r na t) (replaceFun n r na a)
                                  Nothing -> App i (replaceFun n r na t) (replaceFun n r na a)
replaceFun n r na (Lam i x ty t) = Lam i x ty (replaceFun n r na t)
replaceFun n r na (Fix i f fty x xty t) = Fix i f fty x xty (replaceFun n r na t)
replaceFun n r na (IfZ i c t e) = IfZ i (replaceFun n r na c) (replaceFun n r na t) (replaceFun n r na e)
replaceFun n r na (Let i x ty d t) = Let i x ty (replaceFun n r na d) (replaceFun n r na t)
replaceFun n r na (UnaryOp i o t) = UnaryOp i o (replaceFun n r na t)
replaceFun n r na (BinaryOp i o t u) = BinaryOp i o (replaceFun n r na t) (replaceFun n r na u)
replaceFun _ _ _ t = t

doInline :: [TDecl Term] -> [(Name, Term, Int, Int)] -> [TDecl Term]
doInline ts [] = ts
doInline ts ((n, t, i, na):xs) = let ts' = if i < 200    then map (apply2Term (replaceFun n t na)) (deleteFun n ts)
                                                         else ts
                                 in doInline ts' xs
                      
inlineFun :: [TDecl Term] -> [TDecl Term]
inlineFun ts = let (_, table) = runWriter (getFuns ts)
               in doInline ts $ reverse table                  
