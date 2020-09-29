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

module Elab ( elab, elab_decl ) where

import Lang
import Subst

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: NTerm -> Term
elab (V p v)               = V p (Free v)
elab (Const p c)           = Const p c
elab (Lam p v ty t)        = Lam p v ty (close v (elab t))
elab (App p h a)           = App p (elab h) (elab a)
elab (Fix p f fty x xty t) = Fix p f fty x xty (closeN [f, x] (elab t))
elab (IfZ p c t e)         = IfZ p (elab c) (elab t) (elab e)
elab (UnaryOp p o t)       = UnaryOp p o (elab t)

elab_decl :: Decl NTerm -> Decl Term
elab_decl = fmap elab


-- | 'desugar' transforma el AST superficial en un AST interno para
-- eliminar toda la azucar sintáctica

desugar :: STerm -> NTerm
desugar (SV p v)               = V p v
desugar (SConst p c)           = Const p c
desugar (SLam p [] t)          = desugar t
desugar (SLam p (n:ns) t)      = Lam p (fst n) (snd n) (desugar (SLam p ns t))
desugar (SApp p h a)           = App p (desugar h) (desugar a)
--desugar (SFix p [] t)          = error
--desugar (SFix p n:ns t)        = desugarFix p n:ns t
desugar (SIfZ p c t e)         = IfZ p (desugar c) (desugar t) (desugar e)
desugar (SUnaryOp p o t)       = UnaryOp p o (desugar t)
desugar (SLet p x xty d a)             = App p (Lam p x xty (desugar a)) (desugar d)
desugar (SLetFun p f fty nts d a)      = desugar (SLet p f (buildFunType nts fty) (SLam p nts d) a)
    where   buildFunType [] fty            = fty
            buildFunType (n:ns) fty        = FunTy (snd n) (buildFunType ns fty)
desugar (SLetFunRec p f fty [] d a)    = desugar d  -- hay que usar failPosPCF p "La función recursiva debe tener un nombre"
desugar (SLetFunRec p f fty (n:ns) d a) | null ns   = desugar (SLet p f (FunTy (snd n) fty)
                                                      (SFix p f (FunTy (snd n) fty) (fst n) (snd n) d) a)
                                        | otherwise = desugar (SLetFunRec p f (buildFunType ns fty) [n] (SLam p ns d) a)
    where   buildFunType [] fty            = fty
            buildFunType (n:ns) fty        = FunTy (snd n) (buildFunType ns fty)
