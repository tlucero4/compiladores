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

module Elab ( elab, elab_sdecl, desugar ) where

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
elab' (UnaryOp p o t)       = UnaryOp p o (elab' t)

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
    tn <- lookupSTy n
    case tn of
         Just t  -> do  dt <- desugarTy t
                        return (NamedTy n dt)
         _       -> failPosPCF p $ "El tipo "++n++" no existe."

desugar :: MonadPCF m => STerm -> m NTerm
desugar (SV p v)               = return (V p v)
desugar (SConst p c)           = return (Const p c)
desugar (SLam p [] t)          = failPosPCF p $ "La función debe tener un argumento"
desugar (SLam p l t)           = sLam p l t
desugar (SApp p h a)           = 
    case h of
         SUnaryOp p o -> do da <- desugar a
                            return (UnaryOp p o da)
         _            -> do dh <- desugar h
                            da <- desugar a
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
desugar (SUnaryOp p o)         = return (Lam p "x" NatTy (UnaryOp p o (V p "x")))

desugar (SLet p _ _   [] True _ _)  = failPosPCF p $ "La función recursiva debe tener un argumento"
desugar (SLet p n nty [] False d a) = do dd <- desugar d
                                         da <- desugar a
                                         dnty <- desugarTy nty
                                         return (App p (Lam p n dnty da) dd)
desugar (SLet p f fty ns False d a) = desugar (SLet p f (buildFunType ns fty) [] False (SLam p ns d) a)
desugar (SLet p f fty ns True d a)  = desugar (sLet p f fty ns True d a)

{-
desugar (SLet p x xty d a)             = App p (Lam p x xty (desugar a)) (desugar d)
desugar (SLetFun p f fty nts d a)      = 
desugar (SLetFunRec p f fty [] d a)    = failPosPCF p "La función recursiva debe tener un nombre"
desugar (SLetFunRec p f fty (n:ns) d a) | null ns   = desugar (SLet p f (FunTy (snd n) fty)
                                                      (SFix p f (FunTy (snd n) fty) (fst n) (snd n) d) a)
                                        | otherwise = desugar (SLetFunRec p f (buildFunType ns fty) [n] (SLam p ns d) a) 
                                        -}
elab :: MonadPCF m => STerm -> m Term
elab t = do dt <- desugar t
            return (elab' dt)
                                        
elab_sdecl :: MonadPCF m => SDecl STerm -> m (TDecl Term)
elab_sdecl (SDecl p n nty [] _ st)        = do dty <- desugarTy nty
                                               t <- elab st
                                               return (TDecl p n dty t)
elab_sdecl (SDecl p n nty [v] True st)    = do dty <- desugarTy (SFunTy (snd v) nty)
                                               sl <- sLam p [] st
                                               return (TDecl p n dty (elab' sl))
elab_sdecl (SDecl p n nty (v:vs) True st) = elab_sdecl (SDecl p n (buildFunType vs nty) [v] True (SLam p vs st))
elab_sdecl (SDecl p n nty (v:vs) _ st)    = do dty <- desugarTy (buildFunType (v:vs) nty)
                                               l <- elab (SLam p vs st)
                                               return (TDecl p n dty l)
