module CEK where

import Lang
import Global ( GlEnv(..) )
import MonadPCF
import PPrint
import Subst ( substN )
import Common ( Pos(NoPos) )

type Ent = [Val]

-- Frames
data Fr =
      KArg Ent Term
    | KClos Clos
    | KBinOp BinaryOp Term Ent
    | KBinOp' BinaryOp Val
    | KIfZ Ent Term Term
    | KLet Ent Term


type Kont = [Fr]

data Clos = 
      ClosFun Ent Name Ty Term
    | ClosFix Ent Name Ty Name Ty Term

-- | AST de Valores
data Val = 
      N Int 
    | C Clos
    
search :: MonadPCF m => Term -> Ent -> Kont -> m Val
search (BinaryOp _ o t u) e k = search t e ((KBinOp o u e):k)
search (IfZ _ c t u) e k = search c e ((KIfZ e t u):k)
search (App _ t u) e k = search t e ((KArg e u):k)
search (Let _ n _ d a) e k = search d e ((KLet e a):k)

search (V _ (Bound i)) e k = destroy (e !! i) k
search (V _ (Free n)) e k = do
    dn <- lookupDecl n
    case dn of
        Nothing -> failPCF $ "Error de ejecución: variable no declarada: " ++ ppName n 
        Just t -> search t e k
search (Const _ (CNat n)) e k = destroy (N n) k
search (Lam _ x xty t) e k = destroy (C (ClosFun e x xty t)) k
search (Fix _ f fty x xty t) e k = destroy (C (ClosFix e f fty x xty t)) k

destroy :: MonadPCF m => Val -> Kont -> m Val
destroy v [] = return v

destroy (N m) ((KBinOp' Add (N n)):k) = destroy (N (n+m)) k
destroy (N m) ((KBinOp' Prod (N n)):k) = destroy (N (n*m)) k
destroy (N m) ((KBinOp' Sub (N n)):k) = if m > n then destroy (N 0) k
                                                 else destroy (N (n-m)) k


destroy (N 0) ((KIfZ e t u):k) = search t e k
destroy (N _) ((KIfZ e t u):k) = search u e k
destroy (C c) ((KArg e t):k) = search t e ((KClos c):k)
destroy v ((KLet e t):k) = search t (v:e) k
destroy v ((KBinOp o u e):k) = search u e ((KBinOp' o v):k)
destroy v ((KClos c):k) =
    case c of
         (ClosFun e _ _ t) -> search t (v:e) k
         (ClosFix e _ _ _ _ t) -> search t (v:(C c):e) k  
        
eval :: MonadPCF m => Term -> m Term
eval t = do
    v <- search t [] []
    return (vtot v)

-- Value to Term
vtot :: Val -> Term
vtot v =
    case v of
         N n -> Const NoPos (CNat n)
         C c -> case c of
                  ClosFun [] x xty t -> Lam NoPos x xty t
                  ClosFun e  x xty t -> substN (map vtot e) (Lam NoPos x xty t)
                  ClosFix []  f fty x xty t -> Fix NoPos f fty x xty t
                  ClosFix e   f fty x xty t -> substN (map vtot e) (Fix NoPos f fty x xty t)
