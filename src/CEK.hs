module CEK where

import Lang
import Global ( GlEnv(..) )
import MonadPCF

type Ent = [Val]

-- Frames
data Fr =
      KArg Ent Term
    | KClos
    | KSucc
    | KPred
    | KIfZ Ent Term Term

data Kont = [Fr]

-- | AST de Valores
data Val = 
      N Int 
    | ClosFun Ent Var Term
    | ClosFix Ent Name Var Term
    deriving (Show)

    
search :: MonadPCF m => Term -> Ent -> Kont -> m Val
destroy :: MonadPCF m => Term -> Kont -> m Val
