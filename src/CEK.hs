module CEK where

import Lang
import Global ( GlEnv(..) )
import MonadPCF
import PPrint
import Common ( Pos(NoPos) )

type Ent = [Val]

-- Frames
data Fr =
      KArg Ent Term
    | KClos Clos
    | KSucc
    | KPred
    | KIfZ Ent Term Term

type Kont = [Fr]

data Clos = 
      ClosFun Ent Name Term
    | ClosFix Ent Name Name Term
    
-- | AST de Valores
data Val = 
      N Int 
    | C Clos

    
{-

Que hacer con los indices?
Hay que trabajar el tema indices cuando aparece un Lam o un Fix en la fase de REDUCCION?
Es decir, en destroy teniendo una clausura como Valor

Las variables libres (Free ...) si o si tienen que ser variables globales que hay que buscar en Global
Las bound si o si tienen que encontrarse en el entorno que le vamos pasando, con indices de Bruijn como indice de lista.
    
-}    
    
search :: MonadPCF m => Term -> Ent -> Kont -> m Val
search (UnaryOp _ Succ t) e k = search t e (KSucc:k)
search (UnaryOp _ Pred t) e k = search t e (KPred:k)
search (IfZ _ c t u) e k = search c e ((KIfZ e t u):k)
search (App _ t u) e k = search t e ((KArg e u):k)
search (V _ (Bound i)) e k = destroy (e !! i) k
search (V _ (Free n)) e k = do
    dn <- lookupDecl n
    case dn of
        Nothing -> failPCF $ "Error de ejecución: variable no declarada: " ++ ppName n 
        Just t -> search t e k
search (Const _ (CNat n)) e k = destroy (N n) k
search (Lam _ x _ t) e k = destroy (C (ClosFun e x t)) k -- chequear si va name o var
search (Fix _ f _ x _ t) e k = destroy (C (ClosFix e f x t)) k

destroy :: MonadPCF m => Val -> Kont -> m Val
destroy v [] = return v
destroy (N 0) (KPred:k) = destroy (N 0) k
destroy (N n) (KPred:k) = destroy (N (n - 1)) k
destroy (N n) (KSucc:k) = destroy (N (n + 1)) k
destroy (N 0) ((KIfZ e t u):k) = search t e k
destroy (N _) ((KIfZ e t u):k) = search u e k
destroy (C c) ((KArg e t):k) = search t e ((KClos c):k)
destroy v ((KClos c):k) =
    case c of
         (ClosFun e _ t) -> search t (v:e) k
         (ClosFix e _ _ t) -> search t (v:(C c):e) k  
        
eval :: MonadPCF m => Term -> m Term
eval t = do
    v <- search t [] []
    return (vtot v)

vtot :: Val -> Term
vtot v =
    case v of
         N n -> Const NoPos (CNat n)
         C c -> case c of
                  ClosFun [] x t -> Lam NoPos x NatTy t
                  ClosFun e  x t -> Lam NoPos x NatTy (rfv t e)
                  ClosFix []  f x t -> Fix NoPos f NatTy x NatTy t
                  ClosFix [v] f x t -> Fix NoPos f NatTy x NatTy t
                  ClosFix e   f x t -> Fix NoPos f NatTy x NatTy (rfv t e)
                                        
-- Resignify Free Variables
rfv :: Term -> Ent -> Term
rfv t@(V _ (Bound 0)) e = t
rfv t@(V _ (Bound n)) e = vtot (e !! (n-1))
rfv (Lam i n ty t) e = Lam i n ty (rfv t e)
rfv (App i t u) e = App i (rfv t e) (rfv u e)
rfv (UnaryOp i o t) e = UnaryOp i o (rfv t e)
rfv (Fix i f fty x xty t) e = Fix i f fty x xty (rfv t e)
rfv (IfZ i c t u) e = IfZ i (rfv c e) (rfv t e) (rfv u e)
rfv t _ = t

{- Version debug

vtot :: MonadPCF m => Val -> m Term
vtot v =
    case v of
         N n -> return (Const NoPos (CNat n))
         C c -> case c of
                  ClosFun [] x t -> return (Lam NoPos x NatTy t)
                  ClosFun e  x t -> do  tt <- rfv t e
                                        return (Lam NoPos x NatTy tt)
                  ClosFix []  f x t -> return (Fix NoPos f NatTy x NatTy t)
                  ClosFix [v] f x t -> return (Fix NoPos f NatTy x NatTy t)
                  ClosFix e   f x t -> do   tt <- rfv t e
                                            return (Fix NoPos f NatTy x NatTy tt)

                                            
rfv :: MonadPCF m => Term -> Ent -> m Term

rfv t@(V _ (Bound 0)) e = do printPCF ("T " ++ show t )
                           return t
rfv t@(V _ (Bound n)) e = do printPCF ("T " ++ show t )
                           vtot (e !! (n-1))
rfv (Lam i n ty t) e = do printPCF ("T " ++ show t )
                        tt <- rfv t e
                        return (Lam i n ty tt)
rfv (App i t u) e = do printPCF ("T " ++ show t )
                     tt <- rfv t e
                     tu <- rfv u e
                     return (App i tt tu)
rfv (UnaryOp i o t) e = do printPCF ("T " ++ show t )
                         tt <- rfv t e
                         return (UnaryOp i o tt)
rfv (Fix i f fty x xty t) e = do printPCF ("T " ++ show t )
                               tt <- rfv t e
                               return (Fix i f fty x xty tt)
rfv (IfZ i c t u) e = do printPCF ("T " ++ show t )
                       tc <- rfv c e
                       tt <- rfv t e
                       tu <- rfv u e
                       return (IfZ i tc tt tu)
rfv t _ = return t

-}
