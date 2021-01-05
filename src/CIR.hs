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

putLabel :: [BasicBlock] -> Loc -> [BasicBlock]
putLabel [] _ = []
putLabel [(n,i,t)] l = [(n,i,Jump l)]
putLabel (x:xs) l = x : putLabel xs l 

getFreshName :: StateT (Int, [Inst], Loc) (Writer [BasicBlock]) Name
getFreshName = do (k, _, _) <- get
                  modify (\(k, i, l) -> (k+1, i, l))
                  return ("__c_" ++ show k)
                               
mkBlocks :: Ir -> StateT (Int, [Inst], Loc) (Writer [BasicBlock]) Val
mkBlocks (IrVar n) = if (isPrefixOf "__" n) then return $ R $ Temp n else return $ G n
mkBlocks (IrConst (CNat n)) = return $ C n
mkBlocks (IrCall i is) = do v <- mkBlocks i
                            vs <- mapM mkBlocks is -- ???
                            f <- getFreshName
                            let reg = Temp f
                            modify (\(k, i, l) -> (k, i ++ [Assign reg $ Call v vs], l))
                            return $ R (Temp f)
mkBlocks (IrBinaryOp o t u) = do vt <- mkBlocks t
                                 vu <- mkBlocks u
                                 f <- getFreshName
                                 let reg = Temp f
                                 modify (\(k, i, l) -> (k, i ++ [Assign reg $ BinOp o vt vu], l))
                                 return $ R reg
mkBlocks (IrUnaryOp o t) = do vt <- mkBlocks t
                              f <- getFreshName
                              let reg = Temp f
                              modify (\(k, i, l) -> (k, i ++ [Assign reg $ UnOp o vt], l))
                              return $ R reg
mkBlocks (IrLet n d a) = do vd <- mkBlocks d
                            let re1 = Temp n
                            modify (\(k, i, l) -> (k, i ++ [Assign re1 $ CIR.V vd], l))
                            va <- mkBlocks a
                            f <- getFreshName
                            let reg = Temp f
                            modify (\(k, i, l) -> (k, i ++ [Assign reg $ CIR.V va], l))
                            return $ R reg
mkBlocks (IrIfZ c t e) = do vc <- mkBlocks c
                            f <- getFreshName
                            let bt = f++"_then"
                                be = f++"_else"
                                bc = f++"_cont"
                                rvt = Temp $ f++"_t"
                                rve = Temp $ f++"_e"
                                reg = Temp f
                            (_,i1,l1) <- get
                            tell $ [(l1, i1, CondJump (Eq vc $ C 0) bt be)]
                            modify (\(k, i, l) -> (k, [], l))
                            vt <- mkBlocks t
                            (_,i2,l2) <- get
                            let di2 = [Assign rvt $ CIR.V vt]
                            tell $ [(bt, i2 ++ di2, Jump bc)]
                            modify (\(k, i, l) -> (k, [], l))
                            ve <- mkBlocks e
                            (_,i3,l3) <- get
                            let di3 = [Assign rve $ CIR.V ve]
                            tell $ [(be, i3 ++ di3, Jump bc)]
                            modify (\(k, i, l) -> (k, [Assign reg $ Phi [(bt, R rvt), (be, R rve)]] , bc))
                            return $ R reg
mkBlocks (IrMkClosure n is) = do vs <- mapM mkBlocks is
                                 f <- getFreshName
                                 let reg = Temp f
                                 modify (\(k, i, l) -> (k, i ++ [Assign reg $ MkClosure n vs], l))
                                 return $ R (Temp f)
mkBlocks (IrAccess i n) = do v <- mkBlocks i
                             f <- getFreshName
                             let reg = Temp f
                             modify (\(k, i, l) -> (k, i ++ [Assign reg $ Access v n], l))
                             return $ R (Temp f)

mkInstrMain :: Int -> Ir -> Loc -> [Inst] -> Writer [BasicBlock] (Int, Name, [Inst], Val)
mkInstrMain k ir l i = do let ((v , (k', i', l')) , bs) = runWriter (runStateT (mkBlocks ir) (k, i, l))
                          tell $ putLabel bs l'
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
