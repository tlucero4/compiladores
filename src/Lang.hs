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
  deriving (Eq,Show)

data UnaryOp = Succ | Pred | Print
  deriving (Eq,Show)
  
data BinaryOp = Add | Sub | Prod -- prod no usado
  deriving (Eq,Show)

-- | tipos de datos de declaraciones, parametrizado por el tipo del cuerpo de la declaración

data IrDecl = IrFun { irDeclName :: Name, irDeclArity :: Int, irDeclArgNames :: [Name], irDeclBody :: Ir } -- Asignamos un fragmento de codigo estatico a la funcion
            | IrVal { irDeclName :: Name, irDeclDef :: Ir } -- Asignamos una clausura a el nombre de la funcion
    deriving (Show)

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
  | SUnaryOp info UnaryOp
  | SBinaryOp info BinaryOp
  | SInfixBinaryOp info BinaryOp (STm info var)
  | SFix info Name STy Name STy (STm info var)
--  | SFix info [(Name, Ty)] (STm info var)     ¿realmente existe una version de Fix con multiples variables?
  | SIfZ info (STm info var) (STm info var) (STm info var)
  | SLet info Name STy [(Name, STy)] Bool (STm info var) (STm info var)
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
  | BinaryOp info BinaryOp (Tm info var) (Tm info var)
  | UnaryOp info UnaryOp (Tm info var)
  | Fix info Name Ty Name Ty (Tm info var)
  | IfZ info (Tm info var) (Tm info var) (Tm info var)
  | Let info Name Ty (Tm info var) (Tm info var)
  deriving (Show, Functor)

data Ir = IrVar Name
        | IrCall Ir [Ir]
        | IrConst Const
        | IrBinaryOp BinaryOp Ir Ir
        | IrUnaryOp UnaryOp Ir
        | IrLet Name Ir Ir
        | IrIfZ Ir Ir Ir
        | IrMkClosure Name [Ir]
        | IrAccess Ir Int
    deriving (Show)

type STerm = STm Pos Name
type NTerm = Tm Pos Name   -- ^ 'Tm' tiene 'Name's como variables ligadas y libres, guarda posición
type Term = Tm Pos Var     -- ^ 'Tm' con índices de De Bruijn como variables ligadas, different type of variables, guarda posición

data Var = 
    Bound !Int
  | Free Name
  deriving Show
{-
instance Eq Term where
   (==) (V _ (Bound n)) (V _ (Bound m)) = (n == m) -- ???
   (==) (V _ (Free n)) (V _ (Free m)) = (n == m) -- ???
   (==) (Const c) (Const d) = (c == d)
   (==) (Lam _ n _ t) (Lam _ m _ u) = (n == m) && (t == u)
   (==) (App _ t u) (App _ y o) = (t == y) && (u == o)
   (==) (BinaryOp _ o t u) (BinaryOp _ o' t' u') = (o == o') && (t == t') && (u == u')
   (==) (UnaryOp _ o t) (UnaryOp _ o' t') = if (o == Print) then False else (o == o') && (t == t') && (u == u')
   (==) (Fix _ f _ x _ t) (Lam _ g _ y _ u) = (f == g) && (x == y) && (t == u)
   (==) (IfZ _ c t e) (IfZ _ d u i) = (c == d) && (t == u) && (e == i)
   (==) (Let _ _ _ c t) (Let _ _ _ d u) = (c == t) && (d == u)
   (==) _ _ = False
   -}
-- | Obtiene la info en la raíz del término.
getInfo :: Tm info var -> info
getInfo (V i _) = i
getInfo (Const i _) = i
getInfo (Lam i _ _ _) = i
getInfo (App i _ _ ) = i
getInfo (BinaryOp i _ _ _) = i
getInfo (UnaryOp i _ _) = i
getInfo (Fix i _ _ _ _ _) = i
getInfo (IfZ i _ _ _) = i
getInfo (Let i _ _ _ _) = i

-- | Obtiene las variables libres de un término.
freeVars :: Tm info Var -> [Name]
freeVars (V _ (Free v))    = [v]
freeVars (V _ _)           = []
freeVars (Lam _ _ _ t)     = freeVars t
freeVars (App _ l r)       = freeVars l ++ freeVars r
freeVars (BinaryOp _ _ t1 t2) = freeVars t1 ++ freeVars t2
freeVars (UnaryOp _ _ t) = freeVars t
freeVars (Fix _ _ _ _ _ t) = freeVars t
freeVars (IfZ _ c t e)     = freeVars c ++ freeVars t ++ freeVars e
freeVars (Const _ _)       = []
freeVars (Let i _ _ f a)   = freeVars f ++ freeVars a --- ???
