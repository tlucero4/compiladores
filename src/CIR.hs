module CIR where

import Lang
import Data.List (intercalate, isPrefixOf)
import Control.Monad.State.Lazy
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

putEndLabel :: [BasicBlock] -> Loc -> [BasicBlock]
putEndLabel [] _ = []
putEndLabel [(n,i,t)] l = [(n,i,Jump l)]
putEndLabel (x:xs) l = x : putEndLabel xs l

addInstr :: Inst -> StateT (Int, [Inst], Loc) (Writer [BasicBlock]) ()
addInstr i' = modify (\(k, i, l) -> (k, i ++ [i'], l))

getFreshName :: StateT (Int, [Inst], Loc) (Writer [BasicBlock]) Name
getFreshName = do (k, _, _) <- get
                  modify (\(k, i, l) -> (k+1, i, l))
                  return ("__c_" ++ show k)
                  
assignValTo :: Expr -> StateT (Int, [Inst], Loc) (Writer [BasicBlock]) Val
assignValTo e = do  f <- getFreshName
                    let reg = Temp f
                    addInstr (Assign reg e)
                    return $ R reg

-- Seteamos la condición del If
mkCond :: Ir -> Loc -> Loc -> StateT (Int, [Inst], Loc) (Writer [BasicBlock]) ()
mkCond c t e = do vc <- mkBlocks c
                  (_,i,l) <- get
                  tell $ [(l, i, CondJump (Eq vc $ C 0) t e)]
                    
-- Creamos un bloque con la rama del If que corresponde
mkBranch :: Ir -> Loc -> Loc -> StateT (Int, [Inst], Loc) (Writer [BasicBlock]) (Loc, Reg)
mkBranch t l c = do let ret = Temp $ l++"_ret"
                    modify (\(k, _, _) -> (k, [], l))
                    vt <- mkBlocks t
                    (_,i,l') <- get
                    tell $ [(l', i ++ [Assign ret $ CIR.V vt], Jump c)]
                    return (l', ret)
                               
mkBlocks :: Ir -> StateT (Int, [Inst], Loc) (Writer [BasicBlock]) Val
mkBlocks (IrVar n) = if (isPrefixOf "__" n) then return (R $ Temp n) else return $ G n
mkBlocks (IrConst (CNat n)) = return $ C n
mkBlocks (IrCall i is) = do v <- mkBlocks i
                            vs <- mapM mkBlocks is
                            assignValTo $ Call v vs
mkBlocks (IrBinaryOp o t u) = do vt <- mkBlocks t
                                 vu <- mkBlocks u
                                 assignValTo $ BinOp o vt vu
mkBlocks (IrUnaryOp o t) = do vt <- mkBlocks t
                              assignValTo $ UnOp o vt
mkBlocks (IrLet n d a) = do vd <- mkBlocks d
                            addInstr (Assign (Temp n) $ CIR.V vd)
                            va <- mkBlocks a
                            assignValTo $ CIR.V va
mkBlocks (IrMkClosure n is) = do vs <- mapM mkBlocks is
                                 assignValTo $ MkClosure n vs
mkBlocks (IrAccess i n) = do v <- mkBlocks i
                             assignValTo $ Access v n
mkBlocks (IrIfZ c t e) = do f <- getFreshName
                            let reg = Temp f
                                bt = f++"_then"
                                be = f++"_else"
                                bc = f++"_cont"
                            mkCond c bt be
                            (lt, rvt) <- mkBranch t bt bc
                            (le, rve) <- mkBranch e be bc
                            modify (\(k, i, l) -> (k, [Assign reg $ Phi [(lt, R rvt), (le, R rve)]] , bc))
                            return $ R reg

mkInstrMain :: Int -> Ir -> Loc -> [Inst] -> Writer [BasicBlock] (Int, Name, [Inst], Val)
mkInstrMain k ir l i = do let ((v , (k', i', l')) , bs) = runWriter (runStateT (mkBlocks ir) (k, i, l))
                          tell $ putEndLabel bs l'
                          return (k', l', i', v)
      
mkPcfMain :: Int -> [IrDecl] -> Loc -> [Inst] -> [BasicBlock]
mkPcfMain k [] l i = [(l,i, Return $ C 0)]
mkPcfMain k (x:xs) lv instr = let (IrVal n ir) = x
                                  ((k', l, i, v), bs) = runWriter $ mkInstrMain k ir lv instr
                                  i' = i ++ [Store n $ CIR.V v]
                              in bs ++ mkPcfMain k' xs l i'
      
rcFun :: Name -> [Name] -> Ir -> Int -> (CanonFun, Int)
rcFun n a ir i = let ((v , (k', i', l')) , bs) = runWriter (runStateT (mkBlocks ir) (i, [], n++"b"))
                     reg = Temp $ n++"_reg"
                     b = (l', i' ++ [Assign reg $ CIR.V v], Return $ R reg)
                     cf = (n, a, bs++[b])
                 in (cf, k')

rc :: [IrDecl] -> [IrDecl] -> Int -> [Either CanonFun CanonVal]
rc ys []     i = [ Left ("pcfmain", [], mkPcfMain i (reverse ys) "entry" []) ]
rc ys (x:xs) i = case x of
                    IrFun n _ a ir -> let (cf, i') = rcFun n a ir i
                                      in (Left $ cf) : rc ys xs i'
                    IrVal n _      -> (Right n) : rc (x:ys) xs i

runCanon :: [IrDecl] -> CanonProg
runCanon is = CanonProg $ rc [] is 0
