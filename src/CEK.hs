module CEK where

import Lang
import Global ( GlEnv(..) )
import MonadPCF

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

search :: MonadPCF m => Term -> Ent -> Kont -> m Val
search (UnaryOp _ Succ t) e k = search t e (KSucc:k)
search (UnaryOp _ Pred t) e k = search t e (KPred:k)
search (IfZ _ c t u) e k = search c e ((KIfZ e t u):k)
search (App _ t u) e k = search t e ((KArg e u):k)
search (V _ (Bound i)) e k = destroy (e !! i) k
--search (V _ (Free n)) e k = ...
search (Const _ (CNat n)) e k = destroy (N n) k
search (Lam _ x _ t) e k = destroy (C (ClosFun e x t)) k -- chequear si va name o var
search (Fix _ f _ x _ t) e k = destroy (C (ClosFix e f x t)) k

destroy :: MonadPCF m => Val -> Kont -> m Val
destroy (N 0) (KPred:k) = destroy (N 0) k
destroy (N n) (KPred:k) = destroy (N (n - 1)) k
destroy (N n) (KSucc:k) = destroy (N (n + 1)) k
destroy (N 0) ((KIfZ e t u):k) = search t e k
destroy (N _) ((KIfZ e t u):k) = search u e k
destroy (C c) ((KArg e t):k) = search t e ((KClos c):k)
destroy v ((KClos c):k) =
    case c of
         (ClosFun e _ t) -> search t (v:e) k
         (ClosFix e f x t) -> search t ((C c):v:e) k  
