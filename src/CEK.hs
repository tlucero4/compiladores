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
      ClosFun Ent Name Ty Term
    | ClosFix Ent Name Ty Name Ty Term
{-
instance Show Clos where
   show (ClosFun e x t) = "Fun (Ent "++show e++")"++show x++" -> "++show t
   show (ClosFix e f x t) = "Fix (Ent "++show e++")"++show f++" "++show x++" -> "++show t
   -}
-- | AST de Valores
data Val = 
      N Int 
    | C Clos
{-
instance Show Val where
   show (N n) = "( VNat "++show n++")"
   show (C c) = "( VClo "++show c++")"
   -}
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
search (Lam _ x xty t) e k = destroy (C (ClosFun e x xty t)) k
search (Fix _ f fty x xty t) e k = destroy (C (ClosFix e f fty x xty t)) k

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
         (ClosFun e _ _ t) -> search t (v:e) k
         (ClosFix e _ _ _ _ t) -> search t (v:(C c):e) k  
        
eval :: MonadPCF m => Term -> m Term
eval t = do
    v <- search t [] []
    return (vtot v)

--{-
-- Value to Term
vtot :: Val -> Term
vtot v =
    case v of
         N n -> Const NoPos (CNat n)
         C c -> case c of
                  ClosFun [] x xty t -> Lam NoPos x xty t
                  ClosFun e  x xty t -> Lam NoPos x xty (rfv t e 0)
                  ClosFix []  f fty x xty t -> Fix NoPos f fty x xty t
                  ClosFix e   f fty x xty t -> Fix NoPos f fty x xty (rfv t e 0)

-- Resignify Free Variables
rfv :: Term -> Ent -> Int -> Term
rfv t@(V _ (Bound 0)) e k = t
rfv t@(V _ (Bound n)) e k = vtot (e !! (n - 1 + k))
rfv (Lam i n ty t) e k = Lam i n ty (rfv t e (k+1))
rfv (App i t u) e k = App i (rfv t e k) (rfv u e k)
rfv (UnaryOp i o t) e k = UnaryOp i o (rfv t e k)
rfv (Fix i f fty x xty t) e k = Fix i f fty x xty (rfv t e (k+2))
rfv (IfZ i c t u) e k = IfZ i (rfv c e k) (rfv t e k) (rfv u e k)
rfv t _ _ = t
---}


{- Version debug

vtot :: MonadPCF m => Val -> m Term
vtot v =
    case v of
         N n -> return (Const NoPos (CNat n))
         C c -> case c of
                  ClosFun [] x t -> return (Lam NoPos x NatTy t)
                  ClosFun e  x t -> do  printPCF ("Fun con entorno: "++show e++"\nNombre: "++show x++"\nTermino: "++show t++"\n")
                                        tt <- rfv t e
                                        return (Lam NoPos x NatTy tt)
                  ClosFix []  f x t -> return (Fix NoPos f NatTy x NatTy t)
                  ClosFix [v] f x t -> return (Fix NoPos f NatTy x NatTy t)
                  ClosFix e   f x t -> do   printPCF ("Fix con entorno: "++show e++"\nNombre-Arg: "++show f++" "++show x++"\nTermino: "++show t++"\n")
                                            tt <- rfv t e
                                            return (Fix NoPos f NatTy x NatTy tt)

                                            
rfv :: MonadPCF m => Term -> Ent -> m Term

rfv t@(V _ (Bound 0)) e = do    printPCF ("T " ++ show t )
                                return t
rfv t@(V _ (Bound n)) e = do    printPCF ("T " ++ show t )
                                vtot (e !! (n-1))
rfv (Lam i n ty t) e = do   printPCF ("T " ++ show t )
                            tt <- rfv t e
                            return (Lam i n ty tt)
rfv (App i t u) e = do  printPCF ("T " ++ show t )
                        tt <- rfv t e
                        tu <- rfv u e
                        return (App i tt tu)
rfv (UnaryOp i o t) e = do  printPCF ("T " ++ show t )
                            tt <- rfv t e
                            return (UnaryOp i o tt)
rfv (Fix i f fty x xty t) e = do    printPCF ("T " ++ show t )
                                    tt <- rfv t e
                                    return (Fix i f fty x xty tt)
rfv (IfZ i c t u) e = do    printPCF ("T " ++ show t )
                            tc <- rfv c e
                            tt <- rfv t e
                            tu <- rfv u e
                            return (IfZ i tc tt tu)
rfv t _ = return t

-}
