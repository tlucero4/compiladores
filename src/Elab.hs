{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@NTerm) a locally closed (@Term@) 
-}

module Elab ( elab, elab_sdecl, desugar, desugarTy, bc_elab_sdecl ) where

import Lang
import Common ( Pos )
import Subst
import MonadPCF

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab' :: NTerm -> Term
elab' (V p v)               = V p (Free v)
elab' (Const p c)           = Const p c
elab' (Lam p v ty t)        = Lam p v ty (close v (elab' t))
elab' (App p h a)           = App p (elab' h) (elab' a)
elab' (Fix p f fty x xty t) = Fix p f fty x xty (closeN [f, x] (elab' t))
elab' (IfZ p c t e)         = IfZ p (elab' c) (elab' t) (elab' e)
elab' (BinaryOp p o t1 t2)  = BinaryOp p o (elab' t1) (elab' t2)
elab' (Let p n nty f x)     = Let p n nty (elab' f) (close n (elab' x))

---elab_decl :: Decl NTerm -> Decl Term
---elab_decl = fmap elab


-- | 'desugar' transforma el AST superficial en un AST interno para
-- eliminar toda la azucar sintáctica

buildFunType :: [(Name,STy)] -> STy -> STy
buildFunType [] fty            = fty
buildFunType (n:ns) fty        = SFunTy (snd n) (buildFunType ns fty)

sLam :: MonadPCF m => Pos -> [(Name,STy)] -> STerm -> m NTerm
sLam p [] t     = do dt <- desugar t
                     return dt
sLam p (n:ns) t = do nty <- desugarTy (snd n)
                     sl <- sLam p ns t
                     return (Lam p (fst n) nty sl)

sLet :: Pos -> Name -> STy -> [(Name,STy)] -> Bool -> STerm -> STerm -> STerm
sLet p f fty [n]    r d a = SLet p f (SFunTy (snd n) fty) [] False (SFix p f (SFunTy (snd n) fty) (fst n) (snd n) d) a
sLet p f fty (n:ns) r d a = sLet p f (buildFunType ns fty) [n] r (SLam p ns d) a

desugarTy :: MonadPCF m => STy -> m Ty
desugarTy (SNatTy)       = return NatTy
desugarTy (SFunTy t y)   = do   dt <- desugarTy t
                                dy <- desugarTy y
                                return (FunTy dt dy)
desugarTy (SNamedTy p n) = do
    tn <- lookupNTy n
    case tn of
         Just t  -> return (NamedTy n t)
         _       -> failPosPCF p $ "El tipo "++n++" no existe."

desugar :: MonadPCF m => STerm -> m NTerm
desugar (SV p v)               = return (V p v)
desugar (SConst p c)           = return (Const p c)
desugar (SLam p [] t)          = failPosPCF p $ "La función debe tener un argumento"
desugar (SLam p l t)           = sLam p l t
desugar (SApp p h a)           =  do dh <- desugar h
                                     case a of
                                          (SInfixBinaryOp _ o t) -> do  dt <- desugar t
                                                                        return (BinaryOp p o dh dt)
                                          _                      -> do  da <- desugar a
                                                                        return (App p dh da)
-- Fix deberia tener una lista de variables con sus tipos? En la teoria no se usa nunca
desugar (SFix p f fty n nty t) = do dfty <- desugarTy fty
                                    dnty <- desugarTy nty
                                    dt <- desugar t
                                    return (Fix p f dfty n dnty dt)
desugar (SIfZ p c t e)         = do dc <- desugar c
                                    dt <- desugar t
                                    de <- desugar e
                                    return (IfZ p dc dt de)
desugar (SUnaryOp p Succ)         = return (Lam p "x" NatTy (BinaryOp p Add (V p "x") (Const p (CNat 1))))
desugar (SUnaryOp p Pred)         = return (Lam p "x" NatTy (BinaryOp p Sub (V p "x") (Const p (CNat 1))))
desugar (SBinaryOp p o)         = return (Lam p "x" NatTy (Lam p "y" NatTy (BinaryOp p o (V p "x") (V p "y"))))
desugar (SInfixBinaryOp p o t)  = do dt <- desugar t
                                     return (Lam p "x" NatTy (BinaryOp p o (V p "x") dt))
desugar (SLet p _ _   [] True _ _)  = failPosPCF p $ "La función recursiva debe tener un argumento"
desugar (SLet p n nty [] False d a) = do dd <- desugar d
                                         da <- desugar a
                                         dnty <- desugarTy nty
                                         --return (App p (Lam p n dnty da) dd)
                                         return (Let p n dnty dd da)
desugar (SLet p f fty ns False d a) = desugar (SLet p f (buildFunType ns fty) [] False (SLam p ns d) a)
desugar (SLet p f fty ns True d a)  = desugar (sLet p f fty ns True d a)

elab :: MonadPCF m => STerm -> m Term
elab t = do dt <- desugar t
            return (elab' dt)
                                        
elab_sdecl :: MonadPCF m => SDecl STerm -> m (TDecl Term)
elab_sdecl (SDecl p n nty [] _ st)        = do dty <- desugarTy nty
                                               t <- elab st
                                               return (TDecl p n dty t)
elab_sdecl (SDecl p n nty [v] True st)    = do dty <- desugarTy (SFunTy (snd v) nty)
                                               sf <- elab (SFix p n (SFunTy (snd v) nty) (fst v) (snd v) st)
                                               return (TDecl p n dty sf)
elab_sdecl (SDecl p n nty (v:vs) True st) = elab_sdecl (SDecl p n (buildFunType vs nty) [v] True (SLam p vs st))
elab_sdecl (SDecl p n nty vs _ st)    = do  dty <- desugarTy (buildFunType vs nty)
                                            dl <- elab (SLam p vs st)
                                            return (TDecl p n dty dl)

bc_elab_sdecl :: MonadPCF m => [SDecl STerm] -> m ([TDecl Term])
bc_elab_sdecl [] = return []
bc_elab_sdecl ((SType p n t):xs) = do   ns <- lookupNTy n
                                        case ns of
                                                Just _  -> failPosPCF p $ "El tipo "++n++" ya existe."
                                                Nothing -> do   dt <- desugarTy t
                                                                addNTy n dt
                                                                bc_elab_sdecl xs
bc_elab_sdecl (x:xs) = do
        t <- elab_sdecl x
        ts <- bc_elab_sdecl xs
        return (t:ts)
