module CIR where

import Lang
import Data.List (intercalate)
import Control.Monad.Writer.Lazy

newtype Reg = Temp String
  deriving Show

data Val = R Reg | C Int | G Name
  deriving Show

type Loc = String

data Inst =
    Assign Reg Expr
  | Store Name Expr
  deriving Show

data Expr =
    BinOp BinaryOp Val Val
  | UnOp UnaryOp Val
  | Phi [(Loc, Val)]
  | Call Val [Val]
  | MkClosure Loc [Val]
  | V Val
  | Access Val Int
  deriving Show

data Terminator =
    Jump Loc
  | CondJump Cond Loc Loc
  | Return Val
  deriving Show

data Cond =
    Eq Val Val
  deriving Show

type BasicBlock = (Loc, [Inst], Terminator)
type Blocks = [BasicBlock]

type CanonFun = (String, [String], [BasicBlock])
type CanonVal = String -- Sólo el nombre, tipo puntero siempre
newtype CanonProg = CanonProg [Either CanonFun CanonVal]

print :: (Blocks, [Inst], Val) -> String
print (bs, is, v) =
  concatMap printBlock bs ++ show is ++ "\n" ++ show v ++ "\n"

printBlock :: BasicBlock -> String
printBlock (loc, is, t) =
  loc ++ ":\n" ++
  concatMap (\i -> "  " ++ show i ++ "\n") is ++
  show t ++ "\n"

instance Show CanonProg where
  show (CanonProg prog) = concatMap pr1 prog where
    pr1 (Left (f, args, blocks)) =
      f ++ "(" ++ intercalate ", " args ++ ") {\n"
        ++ concatMap printBlock blocks ++ "}\n\n"

    pr1 (Right v) =
      "declare " ++ v ++ "\n\n"


      -- A partir de acá desarrollamos la conversión:

procesar :: Ir -> Writer [Inst] Name
procesar ... = do res <- ...
                  tell (Store fresh_name res)
                  return fresh_name
      
cirexp :: Ir -> Writer [Inst] Expr
cirexp i = undefined
cirexp (IrVar n) = CIR.V (G n)
cirexp (IrConst (CNat c)) = CIR.V (C c)

cirexp (IrCall i is) = 
cirexp (IrBinaryOp o t u) = do  t_reg <- procesar t
                                u_reg <- procesar u
                                return $ BinOp o (V (R t_reg)) (V (R u_reg))
cirexp (IrLet n d a) = 
cirexp (IrIfZ c t e) = 
cirexp (MkClosure n is) = 
cirexp (IrAccess i n) =
      
terminator :: Terminator
terminator = undefined
      
mkBlocks :: Ir -> Writer [BasicBlock] Val
mkBlocks = undefined
mkBlocks (IrVar n) = 
mkBlocks (IrCall i is) = 
mkBlocks (IrConst c) = 
mkBlocks (IrBinaryOp o t u) = BinOp o 
mkBlocks (IrLet n d a) = 
mkBlocks (IrIfZ c t e) = mkCond c ++ mkThen t ++ mkElse e
mkBlocks (MkClosure n is) = 
mkBlocks (IrAccess i n) = 

mkInstrMain :: [IrDecl] -> [Inst]
mkInstrMain [] = []
mkInstrMain ((IrVal n ir):xs) = (Store n $ cirexp ir) : mkInstrMain xs
      
rcFun :: Name -> [Name] -> Ir -> CanonFun
rcFun n a ir = (n, a, mkBlocks ir)
      
runCanon :: [IrDecl] -> CanonProg
runCanon is = CanonProg $ rc [] is -- en el primer argumento de rc llevamos las IrVal para despues construir pcfmain

rc :: [IrDecl] -> [IrDecl] -> [Either CanonFun CanonVal]
rc gs [] = [ Left ("pcfmain", [], [("", mkInstrMain gs, terminator)]) ]
rc ys (x:xs) = case x of
                 IrFun n _ a ir -> (Left $ rcFun n a ir) : rc ys xs
                 IrVal n i      -> (Right n)             : rc (x:ys) xs
