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

module Elab ( elab, elab_sdecl ) where

import Lang
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

buildFunType :: [(Name,Ty)] -> Ty -> Ty
buildFunType [] fty            = fty
buildFunType (n:ns) fty        = FunTy (snd n) (buildFunType ns fty)

sLam :: Pos -> [(Name,Ty)] -> STerm
sLam p [] t     = desugar t
sLam p (n:ns) t = Lam p (fst n) (snd n) (sLam p ns t)

sLet :: STerm -> STerm
sLet (SLet p f fty [n]    True d a) = SLet p f (FunTy (snd n) ty) False (SFix p f (FunTy (snd n) ty) (fst n) (snd n) d) a
sLet (SLet p f fty (n:ns) True d a) = sLet (SLet p f (buildFunType ns fty) [n] True (SLam p ns d) a)

desugarTy :: MonadPCF m => Ty -> m Ty
desugarTy (NatTy)           = NatTy
desugarTy (FunTy t y)       = FunTy (desugarTy t) (desugarTy t)
desugarTy (NamedTy p n t)   = NamedTy p n (desugarTy t)
desugarTy (UntrackedTy p n) =
    case lookupSTy n of
         Nothing -> failPosPCF p "El tipo "++n++" no existe."
         Just t  -> NamedTy p n (desugarTy t)

desugar :: MonadPCF m => STerm -> m NTerm
desugar (SV p v)               = V p v
desugar (SConst p c)           = Const p c
desugar (SLam p [] t)          = failPosPCF p "La función debe tener un argumento"
desugar (SLam p l t)           = sLam p l t
desugar (SApp p h a)           = App p (desugar h) (desugar a)
-- Fix deberia tener una lista de variables con sus tipos? En la teoria no se usa nunca
desugar (SFix p f fty n nty t) = Fix p f (desugarTy fty) n (desugarTy nty) (desugar t)
--desugar (SFix p [] t)          = error
--desugar (SFix p n:ns t)        = desugarFix p n:ns t
desugar (SIfZ p c t e)         = IfZ p (desugar c) (desugar t) (desugar e)
desugar (SUnaryOp p o t)       = UnaryOp p o (desugar t)
desugar (SUnaryOp' p o)        = Lam p (V p "x") NatTy (UnaryOp p o (V p "x"))
desugar (SLet p _ _   []     _ _ _) = failPosPCF p "La función recursiva debe tener un argumento"
desugar (SLet p f fty ns False d a) = desugar (SLet p f (desugarTy.buildFunType ns fty) (SLam p ns d) a)
desugar (SLet p f fty ns True d a)  = desugar.sLet (SLet p f fty ns True d a)

{-
desugar (SLet p x xty d a)             = App p (Lam p x xty (desugar a)) (desugar d)
desugar (SLetFun p f fty nts d a)      = 
desugar (SLetFunRec p f fty [] d a)    = failPosPCF p "La función recursiva debe tener un nombre"
desugar (SLetFunRec p f fty (n:ns) d a) | null ns   = desugar (SLet p f (FunTy (snd n) fty)
                                                      (SFix p f (FunTy (snd n) fty) (fst n) (snd n) d) a)
                                        | otherwise = desugar (SLetFunRec p f (buildFunType ns fty) [n] (SLam p ns d) a) 
                                        -}

elab :: STerm -> Term
elab = elab'.desugar

elab_sdecl :: SDecl STerm -> TDecl Term
elab_sdecl (SDecl p n nty [] _ st)        = TDecl p n (desugarTy nty) (elab st)
elab_sdecl (SDecl p n nty [v] True st)    = TDecl p n (desugarTy (FunTy (snd v) nty)) (elab' (sLam p vs st))
elab_sdecl (SDecl p n nty (v:vs) True st) = elab_sdecl (SDecl p n (desugarTy.buildFunType vs nty) [v] True (SLam p vs st))
elab_sdecl (SDecl p n nty (v:vs) _ st)    = TDecl p n (desugarTy.buildFunType (v:vs) nty) (elab (SLam p vs st))
