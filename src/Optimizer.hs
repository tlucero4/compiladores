
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
numCycles = 3

inlineHeur :: Int
inlineHeur = 100

apply2Term :: (Term -> Term) -> TDecl Term -> TDecl Term
apply2Term f (TDecl p n t b) = TDecl p n t $ f b

optimize :: [TDecl Term] -> [TDecl Term]
optimize = optimizeCycle numCycles
                     
optimizeCycle :: Int -> [TDecl Term] -> [TDecl Term]
optimizeCycle 0 ts = ts
optimizeCycle n ts = let ts' = map (apply2Term arithCalc) ts
                         ts'' = inlineFun ts'
                     in optimizeCycle (n-1) ts''
                        

-- Reducción de expresiones aritméticas y eliminación de código muerto

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

-- Funciones Inline (solo para funciones no recursivas)

getFreshName :: Name -> State Int Name
getFreshName n = do i <- get
                    modify (+1)
                    return ("_" ++ n ++ show i)

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x
                    
addLets :: [(Name, Term,Ty)] -> Term ->  Term
addLets [] t = t
addLets ((n,c,ty):ns) t = addLets ns $ Let NoPos n ty c t
                    
substLamR :: Int -> Int -> [(Name, Term, Ty)] -> [Term] ->  Term -> State Int Term
substLamR _ 0 ns xs t = return $ addLets ns $ closeN (reverse $ map fst3 ns) $ substN xs t
substLamR k j ns xs (Lam _ _ ty t) = case (xs !! k) of
                                        V _ _ -> substLamR (k+1) (j-1) ns xs t
                                        Const _ _ -> substLamR (k+1) (j-1) ns xs t
                                        c ->  do fr <- getFreshName "lv"
                                                 let xs' = let (xs1,xs2) = splitAt k xs
                                                            in (xs1 ++ [V NoPos (Free fr)] ++ tail xs2)
                                                 substLamR (k+1) (j-1) ((fr,c,ty):ns) xs' t
  
getArgs :: Term -> Name -> [Term] -> Maybe [Term]
getArgs (App _ t a) n as = getArgs t n (a:as)
getArgs (V _ (Free n')) n as = if (n == n') then Just as
                                            else Nothing
getArgs _ _ _ = Nothing

replaceFun :: Name -> Term -> Int -> Term -> Term
replaceFun n r na x@(App i t a) = case (getArgs t n [a]) of
                                  Just as -> case r of
                                                  Lam _ _ _ _ -> fst $ runState (substLamR 0 (length as) [] as r) 0
                                                  Fix _ _ _ _ _ t -> fst $ runState (substFixR (na - 1) [] (head as) (tail as) t) 0
                                                  _ -> App i (replaceFun n r na t) (replaceFun n r na a)
                                  Nothing -> App i (replaceFun n r na t) (replaceFun n r na a)
replaceFun n r na (Lam i x ty t) = Lam i x ty (replaceFun n r na t)
replaceFun n r na (Fix i f fty x xty t) = Fix i f fty x xty (replaceFun n r na t)
replaceFun n r na (IfZ i c t e) = IfZ i (replaceFun n r na c) (replaceFun n r na t) (replaceFun n r na e)
replaceFun n r na (Let i x ty d t) = Let i x ty (replaceFun n r na d) (replaceFun n r na t)
replaceFun n r na (UnaryOp i o t) = UnaryOp i o (replaceFun n r na t)
replaceFun n r na (BinaryOp i o t u) = BinaryOp i o (replaceFun n r na t) (replaceFun n r na u)
replaceFun _ _ _ t = t

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
calcSizeOfArgs _ = 0

getFuns :: [TDecl Term] -> Writer [(Name, Term, Int)] ()
getFuns [] = return ()
getFuns (x:xs) = case (tdeclBody x) of
                      Lam _ _ _ _ -> do let s = calcSizeOfFun (tdeclBody x)
                                            nargs = calcSizeOfArgs (tdeclType x)
                                        when (s < inlineHeur) $ tell [(tdeclName x, tdeclBody x, nargs)]
                                        getFuns xs  
                      Fix _ _ _ _ _ _ -> do let s = calcSizeOfFun (tdeclBody x)
                                                nargs = calcSizeOfArgs (tdeclType x)
                                            when (False) $ tell [(tdeclName x, tdeclBody x, nargs)] -- a las funciones recursivas no le hacemos inline
                                            getFuns xs  
                      _ -> getFuns xs

deleteFun :: Name -> [TDecl Term] -> [TDecl Term] -- Por ahora no la usamos
deleteFun _ [] = []
deleteFun n (x:xs) | n == tdeclName x = xs
                   | otherwise        = x : (deleteFun n xs)
                                           
doInline :: [TDecl Term] -> [(Name, Term, Int)] -> [TDecl Term]
doInline ts [] = ts
doInline ts ((n, t, na):xs) = let ts' = map (apply2Term (replaceFun n t na)) (deleteFun n ts)
                              in doInline ts' xs
                      
inlineFun :: [TDecl Term] -> [TDecl Term]
inlineFun ts = let (_, table) = runWriter (getFuns ts)
               in doInline ts $ reverse table                  

-- El inline para funciones recursivas no funciona

delAppFix :: Int -> Term -> Maybe Term
delAppFix k t@(App _ (V _ (Bound k')) u) = if (k + 1 == k') then Just t else Nothing
delAppFix k (App _ t u) = delAppFix k t
delAppFix _ _ = Nothing

substFix :: Term -> Int -> Term -> Term
substFix r k (App i t u) = case delAppFix k t of
                                Just a -> substFix r k a
                                Nothing -> App i (substFix r k t) (substFix r k u)
substFix r k (Lam i x ty t) = Lam i x ty t
substFix r k (Fix i f fty x xty t) = Fix i f fty x xty t
substFix r k (IfZ i c t e) = IfZ i (substFix r k c) (substFix r k t) (substFix r k e)
substFix r k (Let i x ty d t) = Let i x ty (substFix r k d) (substFix r k t)
substFix r k (UnaryOp i o t) = UnaryOp i o (substFix r k t)
substFix r k (BinaryOp i o t u) = BinaryOp i o (substFix r k t) (substFix r k u)
substFix r k t@(V i (Bound n)) = if (n == k) then r else t
substFix _ _ t = t

substFixR :: Int -> [Name] -> Term -> [Term] -> Term -> State Int Term
substFixR k ns fa (a:as) (Lam _ _ _ t) = case a of
                                               V _ _ -> substFixR (k-1) ns fa as $ substFix a k t
                                               Const _ _ -> substFixR (k-1) ns fa as $ substFix a k t
                                               _ ->  do fr <- getFreshName "rv" 
                                                        let it = substFix (V NoPos (Free fr)) k t
                                                        ap <- substFixR (k-1) (fr:ns) fa as it
                                                        return (Let NoPos fr NatTy a ap)
substFixR k ns fa [] t = do fn <- getFreshName "prel"
                            fv <- getFreshName "var"
                            fr <- getFreshName "rv"
                            let (inT, ff) = case fa of
                                                V _ _ -> (App NoPos (V NoPos (Bound 0)) fa, "")
                                                Const _ _ -> (App NoPos (V NoPos (Bound 0)) fa, "")
                                                _ -> (App NoPos (V NoPos (Bound 0)) (V NoPos (Free fr)), fr)
                                letT = Fix NoPos fn NatTy fv NatTy t
                            return $ if null ff then closeN (reverse ns) (Let NoPos fn NatTy letT inT)
                                                else Let NoPos ff NatTy fa $ closeN (ff:reverse ns) (Let NoPos fn NatTy letT inT)
