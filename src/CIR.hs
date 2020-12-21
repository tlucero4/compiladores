module CIR where

import Lang
import Data.List (intercalate)
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
getFreshName :: Name -> StateT Int (Writer [BasicBlock]) Name
getFreshName n = do i <- get
                    modify (+1)
                    return ("_" ++ n ++ show i)

mkCallBlocks :: Name -> Val -> [Val] -> [BasicBlock]
mkCallBlocks n vf vas = let reg = Temp n
                            c = n++"_entry"
                        in [(c, [Assign reg $ Call vf vas], undefined)]
                    
mkAccessBlocks :: Name -> Val -> Int -> [BasicBlock]
mkAccessBlocks n v i = let reg = Temp n
                           b = n++"_entry"
                       in [(b, [Assign reg $ Access v i], Return $ R reg)]
                    
mkBinOpBlocks :: Name -> BinaryOp -> Val -> Val -> [BasicBlock]
mkBinOpBlocks n o v1 v2 = let reg = Temp n
                              b = n++"_entry"
                          in [(b, [Assign reg $ BinOp o v1 v2], Return $ R reg)]
                          
mkIfZBlocks :: Name -> Val -> Val -> Val -> [BasicBlock]
mkIfZBlocks n vc vt ve = let reg = Temp n
                             c = n++"_cond"
                             t = n++"_then"
                             e = n++"_else"
                             ic = n++"_ifcont"
                             regt = Temp $ n++"t"
                             rege = Temp $ n++"e"
                             cond = Eq vc $ C 0
                         in [(c, [], CondJump cond t e),
                             (t, [Assign regt $ CIR.V vt], Jump ic),
                             (e, [Assign rege $ CIR.V ve], Jump ic),
                             (ic, [Assign reg $ Phi [(t, R regt), (e, R rege)]], Return $ R reg)]
                               
mkBlocks :: Ir -> StateT Int (Writer [BasicBlock]) Val
mkBlocks (IrVar n) = return $ G n
mkBlocks (IrConst (CNat n)) = return $ C n
mkBlocks (IrCall i is) = do v <- mkBlocks i
                            vs <- mapM mkBlocks is -- ???
                            f <- getFreshName "call"
                            tell $ mkCallBlocks f v vs
                            return $ R (Temp f)
mkBlocks (IrBinaryOp o t u) = do vt <- mkBlocks t
                                 vu <- mkBlocks u
                                 f <- getFreshName "binop"
                                 tell $ mkBinOpBlocks f o vt vu
                                 return $ R (Temp f)
mkBlocks (IrLet n d a) = undefined
mkBlocks (IrIfZ c t e) = do vc <- mkBlocks c
                            vt <- mkBlocks t
                            ve <- mkBlocks e
                            f <- getFreshName "ifz"
                            tell $ mkIfZBlocks f vc vt ve
                            return $ R (Temp f)
mkBlocks (Lang.MkClosure n is) = undefined
mkBlocks (IrAccess i n) = do v <- mkBlocks i
                             f <- getFreshName "access"
                             tell $ mkAccessBlocks f v n
                             return $ R (Temp f)

mkInstrMain :: Int -> [IrDecl] -> Writer [BasicBlock] [Inst]
mkInstrMain i [] = return []
mkInstrMain i ((IrVal n ir):xs) = do let ((v , i') , bs) = runWriter (runStateT (mkBlocks ir) i)
                                     tell bs
                                     is <- mkInstrMain (i' + 1) xs
                                     return $ (Store n $ CIR.V v) : is
      
rcFun :: Name -> [Name] -> Ir -> Int -> (CanonFun, Int)
rcFun n a ir i = let ((v , i') , bs) = runWriter (runStateT (mkBlocks ir) i)
                     cf = (n, a, bs)
                 in (cf, i')
      
runCanon :: [IrDecl] -> CanonProg
runCanon is = CanonProg $ rc [] is 0 -- en el primer argumento de rc llevamos las IrVal para despues construir pcfmain

rc :: [IrDecl] -> [IrDecl] -> Int -> [Either CanonFun CanonVal]
--rc gs [] i = [ Left ("pcfmain", [], [("undefined", mkInstrMain i gs, Jump "ultimaEtiqueta")]) ]
rc gs p@[IrVal n _] i = let (is, bs) = runWriter $ mkInstrMain i (gs++p)
                        in [ Right n, Left ("pcfmain", [], bs++[("entry", is, Return $ G n)] ) ]
rc ys (x:xs) i = case x of
                    IrFun n _ a ir -> let (cf, i') = rcFun n a ir i
                                      in (Left $ cf) : rc ys xs i'
                    IrVal n _      -> (Right n) : rc (x:ys) xs i
