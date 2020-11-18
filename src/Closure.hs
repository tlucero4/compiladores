module Closure (runCC) where

import Lang 
import Subst
import Data.List
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy

getFreshName :: Name -> StateT Int (Writer [IrDecl]) Name
getFreshName n = do i <- get
                    modify (+1)
                    return ("__" ++ n ++ show i)


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
closureConvert (IfZ _ c t u) = do ccc <- closureConvert c
                                  cct <- closureConvert t
                                  ccu <- closureConvert u
                                  return (IrIfZ ccc cct ccu)
closureConvert (Let _ n _ t u) = do cn <- getFreshName n
                                    cct <- closureConvert t
                                    ccu <- closureConvert (open cn u)
                                    return (IrLet n cct ccu)
closureConvert (App _ f x) = do  ccf <- closureConvert f
                                 ccx <- closureConvert x
                                 return (IrCall (IrAccess ccf 0) [ccf,ccx])
closureConvert x@(Lam _ n _ t) = do idn <- getFreshName ""
                                    fn <- getFreshName n
                                    fc <- getFreshName "clo"
                                    cct <- closureConvert (open fn t)
                                    let fv = (freshVars . freeVars) x
                                        idan = [fc,fn]
                                        ida = length idan
                                        idb = makeBlock fv 1 fc cct
                                        fvc = fmap (\n -> IrVar n) fv
                                    tell [(IrFun idn ida idan idb)]
                                    return (MkClosure idn fvc)
closureConvert (Fix _ f _ x _ t) = undefined


runCC :: [TDecl Term] -> Int -> [IrDecl]
runCC [] _ = []
runCC ((TDecl _ n _ b) : xs) i = let ((v , i') , auxDecls) = runWriter (runStateT (closureConvert b) i)
                                 in auxDecls ++ [(IrVal n v)] ++ runCC xs (i'+1)
