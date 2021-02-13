module Closure (runCC) where

import Lang 
import Subst
import Data.List
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy

getFreshName :: Monad m => Name -> StateT Int m Name
getFreshName n = do i <- get
                    modify (+1)
                    return ("__" ++ n ++ show i)

rmDups :: [Name] -> [Name]
rmDups [] = []
rmDups (x:xs) = if elem x xs then rmDups xs else (x : rmDups xs)
                    
makeBlock :: [Name] -> Int -> Name -> Ir -> Ir
makeBlock [] _ _ t = t
makeBlock (x:xs) i c t = (makeBlock xs (i+1) c (IrLet x (IrAccess (IrVar c) i) t))

freshVars :: [Name] -> [Name]
freshVars = filter $ isPrefixOf "__"

closureConvert :: Term -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Free n)) = return (IrVar n)
closureConvert (Const _ c) = return (IrConst c)
closureConvert (BinaryOp _ o t u) = do cct <- closureConvert t
                                       ccu <- closureConvert u
                                       return (IrBinaryOp o cct ccu)
closureConvert (UnaryOp _ o t) = do cct <- closureConvert t
                                    return (IrUnaryOp o cct)
closureConvert (IfZ _ c t u) = do ccc <- closureConvert c
                                  cct <- closureConvert t
                                  ccu <- closureConvert u
                                  return (IrIfZ ccc cct ccu)
closureConvert (Let _ n _ t u) = do cn <- getFreshName n
                                    cct <- closureConvert t
                                    ccu <- closureConvert (open cn u)
                                    return (IrLet cn cct ccu)
closureConvert (App _ f x) = do  ccf <- closureConvert f
                                 ccx <- closureConvert x
                                 return (IrCall (IrAccess ccf 0) [ccf,ccx])
closureConvert c@(Lam _ n _ t) = do idn <- getFreshName ""
                                    fn <- getFreshName n
                                    fc <- getFreshName "clo"
                                    cct <- closureConvert (open fn t)
                                    let fv = (rmDups . freshVars . freeVars) c
                                        idan = [fc,fn]
                                        ida = length idan
                                        idb = makeBlock fv 1 fc cct
                                        fvc = fmap (\n -> IrVar n) fv
                                    tell [(IrFun idn ida idan idb)]
                                    return (IrMkClosure idn fvc)
closureConvert c@(Fix _ f _ x _ t) = do idn <- getFreshName ""
                                        fn <- getFreshName f
                                        fx <- getFreshName x
                                        fc <- getFreshName "clo"
                                        cct <- closureConvert (openN [fn,fx] t)
                                        let fv = (rmDups . freshVars . freeVars) c
                                            idan = [fc,fx]
                                            ida = length idan
                                            idb = IrLet fn (IrVar fc) (makeBlock fv 1 fc cct)
                                            fvc = fmap (\n -> IrVar n) fv
                                        tell [(IrFun idn ida idan idb)]
                                        return (IrMkClosure idn fvc)


runCC :: [TDecl Term] -> Int -> [IrDecl]
runCC [] _ = []
runCC ((TDecl _ n _ b) : xs) i = let ((v , i') , auxDecls) = runWriter (runStateT (closureConvert b) i)
                                 in auxDecls ++ [(IrVal n v)] ++ runCC xs (i'+1)
