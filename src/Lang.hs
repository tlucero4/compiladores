{-# LANGUAGE DeriveFunctor #-}

{-|
Module      : Lang
Description : AST de términos, declaraciones y tipos
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Definiciones de distintos tipos de datos:
  - AST de términos
  - Declaraciones
  - Tipos
  - Variables

-}

module Lang where

import Common ( Pos )

-- | AST de Tipos
data Ty = 
      NatTy 
    | FunTy Ty Ty
    | NamedTy Name Ty
    deriving (Show)
    
instance Eq Ty where
   (==) NatTy NatTy = True
   (==) (FunTy a b) (FunTy c d) = (a == c) && (b == d)
   (==) (NamedTy n t) u = (t == u)
   (==) t (NamedTy n u) = (t == u)
   (==) _ _ = False
    
-- | AST Azucarado de Tipos
data STy = 
      SNatTy
    | SFunTy STy STy
    | SNamedTy Pos Name
    deriving (Show)
    
type Name = String

data Const = CNat Int
  deriving Show

data UnaryOp = Succ | Pred
  deriving Show
  
data BinaryOp = Sum | Sub
  deriving Show

-- | tipos de datos de declaraciones, parametrizado por el tipo del cuerpo de la declaración
data Decl a = Decl { declPos :: Pos, declName :: Name, declBody :: a }
  deriving (Show,Functor)

data TDecl a = TDecl { tdeclPos :: Pos, tdeclName :: Name, tdeclType :: Ty, tdeclBody :: a }
  deriving (Show,Functor)
  
data SDecl a =
    SDecl { sDeclPos :: Pos, sDeclName :: Name, sDeclType :: STy, sDeclVars :: [(Name, STy)], sDeclRec :: Bool, sDeclBody :: a }
  | SType { sDeclPos :: Pos, sNameType :: Name, sSynType :: STy }
  deriving (Show,Functor)
  
-- | AST superficial de los terminos. Es el que usamos para parsear la azucar sintáctica.
data STm info var =
    SV info var
  | SConst info Const
  | SLam info [(Name, STy)] (STm info var) 
  | SApp info (STm info var) (STm info var)
  | SUnaryOp info UnaryOp -- operaciones sin aplicar
  | SFix info Name STy Name STy (STm info var)
--  | SFix info [(Name, Ty)] (STm info var)     ¿realmente existe una version de Fix con multiples variables?
  | SIfZ info (STm info var) (STm info var) (STm info var)
  | SLet info Name STy [(Name, STy)] Bool (STm info var) (STm info var)
  | SBinaryOp info BinaryOp
  deriving (Show, Functor)
  
-- | AST de los términos. 
--   - info es información extra que puede llevar cada nodo. 
--       Por ahora solo la usamos para guardar posiciones en el código fuente.
--   - var es el tipo de la variables. Es 'Name' para fully named y 'Var' para locally closed. 
data Tm info var = 
    V info var
  | Const info Const
  | Lam info Name Ty (Tm info var)
  | App info (Tm info var) (Tm info var)
  | UnaryOp info UnaryOp (Tm info var)
  | Fix info Name Ty Name Ty (Tm info var)
  | IfZ info (Tm info var) (Tm info var) (Tm info var)
  | Let info Name Ty (Tm info var) (Tm info var)
  | BinaryOp info BinaryOp (Tm info var) (Tm info var)
  deriving (Show, Functor)

type STerm = STm Pos Name
type NTerm = Tm Pos Name   -- ^ 'Tm' tiene 'Name's como variables ligadas y libres, guarda posición
type Term = Tm Pos Var     -- ^ 'Tm' con índices de De Bruijn como variables ligadas, different type of variables, guarda posición

data Var = 
    Bound !Int
  | Free Name
  deriving Show

-- | Obtiene la info en la raíz del término.
getInfo :: Tm info var -> info
getInfo (V i _) = i
getInfo (Const i _) = i
getInfo (Lam i _ _ _) = i
getInfo (App i _ _ ) = i
getInfo (UnaryOp i _ _) = i
getInfo (BinaryOp i _ _ _) = i
getInfo (Fix i _ _ _ _ _) = i
getInfo (IfZ i _ _ _) = i
getInfo (Let i _ _ _ _) = i

-- | Obtiene las variables libres de un término.
freeVars :: Tm info Var -> [Name]
freeVars (V _ (Free v))    = [v]
freeVars (V _ _)           = []
freeVars (Lam _ _ _ t)     = freeVars t
freeVars (App _ l r)       = freeVars l ++ freeVars r
freeVars (UnaryOp _ _ t)   = freeVars t
freeVars (BinaryOp _ _ t1 t2) = freeVars t1 ++ freeVars t2
freeVars (Fix _ _ _ _ _ t) = freeVars t
freeVars (IfZ _ c t e)     = freeVars c ++ freeVars t ++ freeVars e
freeVars (Const _ _)       = []
freeVars (Let i _ _ f a)   = freeVars f ++ freeVars a --- ???
