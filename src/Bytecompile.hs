{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Byecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental
Este módulo permite compilar módulos a la BVM. También provee una implementación de la BVM 
para ejecutar bytecode.
-}
module Bytecompile
(Bytecode, bytecompileModule, runBC, bcWrite, bcRead )
 where

import Lang 
import Subst
import MonadPCF

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )
newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go 
    where go =  
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)
                      

type Opcode = Int
type Bytecode = [Int]

data Val = I Int | Fun Env Bytecode | RA Env Bytecode
instance Show Val where
   show (I n) = "( Nat "++show n++")"
   show (Fun e b) = "( Fun with env "++show e++", bytecode "++show b++")"
   show (RA e b) = "( RA with env "++show e++", bytecode "++show b++")"

type Env = [Val]
type Stack = [Val]



{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:
 
   f (CALL : cs) = ...
 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.
 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern SUM      = 6
pattern SUB      = 7
pattern IFZ      = 8
pattern FIX      = 9
pattern STOP     = 10
pattern JUMP     = 11
pattern SHIFT    = 12
pattern DROP     = 13
pattern PRINT    = 14

bc :: MonadPCF m => Term -> m Bytecode
bc (V _ (Bound i)) = return ([ACCESS, i])
bc (V _ (Free _)) = failPCF $ "Error de compilación: No debería haber variables libres."
bc (Const _ (CNat n)) = return([CONST, n])
bc (BinaryOp _ Sum t1 t2) = do
    bt1 <- bc t1
    bt2 <- bc t2
    return (bt1++bt2++[SUM])
bc (BinaryOp _ Sub t1 t2) = do
    bt1 <- bc t1
    bt2 <- bc t2
    return (bt1++bt2++[SUB])
bc (App _ f a) = do
    bf <- bc f
    ba <- bc a
    return (bf++ba++[CALL])
bc (Lam _ v vty t) = do -- v no se usa
    bt <- bc t
    let size = length bt
    return ([FUNCTION, size+1]++bt++[RETURN])
bc (Fix _ f fty v vty t) = do -- f y v no se usan
    bt <- bc t
    let size = length bt
    return ([FUNCTION, size+1]++bt++[RETURN,FIX]) -- Por ahora en vez de FUNCTION usamos FIXPOINT
bc (IfZ _ d t e) = do
    bd <- bc d
    bt <- bc t
    be <- bc e
    let (st, se) = (length bt, length be)
    return (bd++[IFZ, st+2]++bt++[JUMP, se]++be)
bc (Let _ _ _ t1 t2) = do
    bt1 <- bc t1
    bt2 <- bc t2
    return (bt1++[SHIFT]++bt2++[DROP])

bytecompileModule :: MonadPCF m => [TDecl Term] -> m Bytecode
bytecompileModule decls = do
    term <- prog2term decls
    bytecode <- bc term
    return (bytecode++[PRINT,STOP])

prog2term :: MonadPCF m => [TDecl Term] -> m Term
prog2term [] = failPCF $ "Programa vacío"
prog2term [(TDecl _ _ _ t)] = return t
prog2term ((TDecl p n nty t):xs) = do
    txs <- prog2term xs
    return (Let p n nty t (close n txs))

-- | Toma un bytecode, lo codifica y lo escribe un archivo 
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = map fromIntegral <$> un32  <$> decode <$> BS.readFile filename

runBC :: MonadPCF m => Bytecode -> m ()
runBC c = runBC' c [] []

runBC' :: MonadPCF m => Bytecode -> Env -> Stack -> m ()
runBC' [] _ _ = failPCF $ "Error de ejecución: No hay instrucciones."
runBC' (PRINT : cs) e s@(I n : _) = do
    printPCF ("El resultado es "++(show n))
    runBC' cs e s
runBC' (PRINT : _) _ _ = failPCF $ "Error de ejecución: Solo se pueden imprimir naturales."
runBC' (STOP : _) _ _ = do
    printPCF "El programa ha finalizado.\n"
    return ()
runBC' (CONST : n : cs) e s = runBC' cs e (I n : s)
runBC' (SUM : cs) e (I n2 : I n1 : ss) = runBC' cs e (I (n1+n2) : ss)
runBC' (SUB : cs) e (I n2 : I n1 : ss) = if (n1 > n2) then runBC' cs e (I (n1-n2) : ss)
                                                      else runBC' cs e (I 0 : ss)
runBC' (ACCESS : i : cs) e ss = runBC' cs e (e!!i : ss)
runBC' (CALL : cs) e (v : (Fun ef cf) : ss) = runBC' cf (v : ef) ((RA e cs) : ss)
runBC' (FUNCTION : l : cs) e ss = runBC' (drop l cs) e ((Fun e cs) : ss)
runBC' (RETURN : _) _ (v : (RA e cs) : ss) = runBC' cs e (v : ss)
runBC' (FIX : cs) e ((Fun ef cf) : ss) = do
    let efix = ((Fun efix cf) : e)
    runBC' cs e ((Fun efix cf) : ss)
runBC' (SHIFT : cs) e (v : ss) = runBC' cs (v : e) ss
runBC' (DROP : cs) (v : e) s = runBC' cs e s
runBC' (IFZ : l : cs) e (I 0 : ss) = runBC' cs e ss
runBC' (IFZ : l : cs) e (I _ : ss) = runBC' (drop l cs) e ss
runBC' (JUMP : l : cs) e ss = runBC' (drop l cs) e ss
runBC' _ _ _ = failPCF $ "Error de ejecución: Secuencia de instrucciones inválida."


{- Version para debugear
runBC' :: MonadPCF m => Bytecode -> Env -> Stack -> m ()
runBC' [] _ _ = failPCF $ "Error de compilación: No hay instrucciones."
runBC' (PRINT : cs) e s@(I n : _) = do
    printPCF ("El resultado es "++(show n))
    runBC' cs e s
runBC' (PRINT : _) _ _ = failPCF $ "Error de compilación: Solo se pueden imprimir naturales."
runBC' (STOP : _) _ _ = do
    printPCF "El programa ha finalizado."
    return ()
runBC' (CONST : n : cs) e s = do
    printPCF ("\nACTUAL: Const "++(show n)++", next: "++(show cs))
    printPCF ("NEXT e: "++show e++", NEXT s: "++show (I n:s))
    runBC' cs e (I n : s)
runBC' (SUCC : cs) e (I n : ss) = do
    printPCF ("\nACTUAL: Succ"++", next: "++(show cs))
    printPCF ("NEXT e: "++show e++", NEXT s: "++show (I (n+1):ss))
    runBC' cs e (I (n+1) : ss)
runBC' (PRED : cs) e (I n : ss) = do
    printPCF ("\nACTUAL: Pred"++", next: "++(show cs))
    printPCF ("NEXT e: "++show e++", NEXT s: "++show (I (n-1):ss))
    runBC' cs e (I (n-1) : ss)
runBC' (ACCESS : i : cs) e ss = do
    printPCF ("\nACTUAL: Access"++(show i)++", next: "++(show cs))
    printPCF ("NEXT e: "++show e++", NEXT s: "++show (e!!i : ss))
    runBC' cs e (e!!i : ss)
runBC' (CALL : cs) e (v : (Fun ef cf) : ss) = do
    printPCF ("\nACTUAL: CALL"++", next: "++(show cf))
    printPCF ("NEXT e: "++show (v : ef)++", NEXT s: "++show ((RA e cs) : ss))
    runBC' cf (v : ef) ((RA e cs) : ss)
runBC' (FUNCTION : l : cs) e ss = do
    printPCF ("\nACTUAL: Function of length"++(show l)++", next: "++(show (drop l cs)))
    printPCF ("NEXT e: "++show e++", NEXT s: "++show ((Fun e cs) : ss))
    runBC' (drop l cs) e ((Fun e cs) : ss)
runBC' (RETURN : _) _ (v : (RA e cs) : ss) = do
    printPCF ("\nACTUAL: RETURN"++", next: "++(show cs))
    printPCF ("NEXT e: "++show e++", NEXT s: "++show (v : ss))
    runBC' cs e (v : ss)
runBC' (FIXPOINT : l : cs) e ss = do
    let efix = ((Fun efix cs) : e)
    printPCF ("\nACTUAL: FIXPOINT"++", next: "++(show (drop l cs)))
    printPCF ("NEXT e: "++show e++", NEXT s: "++show ((Fun efix cs) : ss))
    runBC' (drop l cs) e ((Fun efix cs) : ss)
--runBC' (FIX : _) _ s@((Fun ef cf) : _) = runBC' cf ef s
runBC' (SHIFT : cs) e (v : ss) = do
    printPCF ("\nACTUAL: SHIFT"++", next: "++(show cs))
    printPCF ("NEXT e: "++show (v : e)++", NEXT s: "++show ss)
    runBC' cs (v : e) ss
runBC' (DROP : cs) (v : e) s = do
    printPCF ("\nACTUAL: DROP"++", next: "++(show cs))
    printPCF ("NEXT e: "++show e++", NEXT s: "++show s)
    runBC' cs e s
runBC' (IFZ : l : cs) e (I 0 : ss) = do
    printPCF ("\nACTUAL: IFZ con 0"++", next: "++(show cs))
    printPCF ("NEXT e: "++show e++", NEXT s: "++show ss)
    runBC' cs e ss
runBC' (IFZ : l : cs) e (I _ : ss) = do
    printPCF ("\nACTUAL: IFZ con np"++", next: "++(show (drop l cs)))
    printPCF ("NEXT e: "++show e++", NEXT s: "++show ss)
    runBC' (drop l cs) e ss
runBC' (JUMP : l : cs) e ss = do
    printPCF ("\nACTUAL: JUMP"++", next: "++(show (drop l cs)))
    printPCF ("NEXT e: "++show e++", NEXT s: "++show ss)
    runBC' (drop l cs) e ss
    -}
