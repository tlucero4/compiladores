
module Optimizer (
   optimize
   ) where

import Lang
import Subst
import Control.Monad.State.Lazy

#define NUM_CYCLES 3
#define MAX_OCURR_INLINE 2

apply2Term :: (Term -> Term) -> TDecl Term -> TDecl Term
apply2Term f (TDecl p n t b) = TDecl p n t $ f b

optimize :: MonadPCF => [TDecl Term] -> [TDecl Term]
optimize = optimizeCycle NUM_CYCLES
                     
optimizeCycle :: MonadPCF => Int -> [TDecl Term] -> [TDecl Term]
optimizeCycle 0 ts = ts
optimizeCycle n ts = do let ts' = map (apply2Term arithCalc) ts
                            ts'' = map (apply2Term commonSubExpr) ts'
                        ts'''   <- inlineFun ts''
                        nts     <- optimizeCycle (n-1) ts'''
                        return nts
                        

-- Reducing Arithmetic Expressions:

arithCalc :: Term -> Term
arithCalc (Lam i n ty t) = Lam i n ty (arithCalc t)
arithCalc (App i t u) = App i (arithCalc t) (arithCalc u)
arithCalc (Fix i f fty n nty t) = Fix i f fty n nty (arithCalc t)
arithCalc (IfZ i c t e) = IfZ i (arithCalc c) (arithCalc t) (arithCalc e)
arithCalc (Let i n ty d t) = Let i n ty (arithCalc d) (arithCalc t)
arithCalc (UnaryOp i o t = UnaryOp i o (arithCalc t)
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

calcTable :: Term -> StateT [Name, Int] ()
calcTable (Lam _ _ _ t) = calcTable t
calcTable (App _ t u) = case t of
                             V (Free n) -> do modify -- buscar n en la tabla y sumarle 1 a su valor
                                              calcTable u
                             otherwise  -> calcTable t
                                           calcTable u
calcTable (Fix _ _ _ _ _ t) = calcTable t
calcTable (IfZ _ c t e) = do calcTable c
                             calcTable t
                             calcTable e
calcTable (Let _ _ _ d t) = do calcTable d
                                calcTable t
calcTable (UnaryOp _ _ t) = calcTable t
calcTable (BinaryOp _ _ t u) = do calcTable t
                                  calcTable u

tableOfApps :: [TDecl Term] -> StateT [Name, Int] ()
tableOfApps [] = return ()
tableOfApps ((TDecl _ _ _ b):xs) = do calcTable b
                                      tableOfApps xs

inlineFun :: MonadPCF => [TDecl Term] -> [TDecl Term]
inlineFun ts = do initTable <- [xxx] -- crear tabla inicial con cada nombre de funcion y valor 0
                  (table, _) <- runStateT (tableOfApps ts) initTable
                  -- filtrar tabla para aquellas aplicaciones que se hagan menos de MAX_OCURR_INLINE veces
                  -- para aquellas funciones que quedaron filtradas, reemplazar su App en el codigo por la definicion
                  
---------
