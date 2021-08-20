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
pattern PROD     = 8
pattern IFZ      = 9
pattern FIX      = 10
pattern STOP     = 11
pattern JUMP     = 12
pattern SHIFT    = 13
pattern DROP     = 14
pattern PRINT    = 15
pattern TAILCALL = 16

-- | 'bct' compila un tértmino en posición de cola, donde se
-- considera reglas especiales cuando se debe convertir una aplicación
bct :: MonadPCF m => Term -> m Bytecode
bct (App _ f a) = do
    bf <- bc f
    ba <- bc a
    return (bf++ba++[TAILCALL])
-- y un condicional, donde se deben compilar en posición de cola sus ramas
bct (IfZ _ d t e) = do
    bd <- bc d
    bt <- bct t
    be <- bct e
    let (st, se) = (length bt, length be)
    return (bd++[IFZ, st]++bt++be)
-- y un let, ya que la instrucción DROP también se puede obviar antes de un RETURNs
bct (Let _ _ _ t1 t2) = do
    bt1 <- bc t1
    bt2 <- bct t2
    return (bt1++[SHIFT]++bt2)
-- en cualquier otro caso, se hace una compilación normal
bct t = do
    bt <- bc t
    return (bt++[RETURN])

-- | 'bc' convierte un término con estructura de árbol
-- en un programa secuencial estructurado como una lista de enteros
bc :: MonadPCF m => Term -> m Bytecode
bc (V _ (Bound i)) = return ([ACCESS, i])
bc (V _ (Free _)) = failPCF $ "Error de compilación: No debería haber variables libres."
bc (Const _ (CNat n)) = return([CONST, n])
bc (BinaryOp _ Add t1 t2) = do
    bt1 <- bc t1
    bt2 <- bc t2
    return (bt1++bt2++[SUM])
bc (BinaryOp _ Prod t1 t2) = do
    bt1 <- bc t1
    bt2 <- bc t2
    return (bt1++bt2++[PROD])
bc (BinaryOp _ Sub t1 t2) = do
    bt1 <- bc t1
    bt2 <- bc t2
    return (bt1++bt2++[SUB])
bc (App _ f a) = do
    bf <- bc f
    ba <- bc a
    return (bf++ba++[CALL])
bc (Lam _ _ _ t) = do -- v no se usa
    bt <- bct t
    let size = length bt
    return ([FUNCTION, size]++bt)
bc (Fix _ _ _ _ _ t) = do -- f y v no se usan
    bt <- bct t
    let size = length bt
    return ([FUNCTION, size]++bt++[FIX])
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

-- | 'prog2term' convierte un programa como lista de declaraciones
-- a un programa con un único término, usando let-bindings
-- ya que para poder convertir el programa en un bytecode
-- solo nos debe importar el resultado de la última definición top-level
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

-- | 'runBC' toma la lista de enteros y va ejecutando el programa secuencialmente
-- Una optimización agregada luego será reemplazar esta función e implementar la
-- maquina virtual en C, donde cada instrucción tiene un coste mas bajo al estar
-- implementada en un lenguaje de bajo nivel
runBC :: MonadPCF m => Bytecode -> m ()
runBC c = runBC' c [] []

runBC' :: MonadPCF m => Bytecode -> Env -> Stack -> m ()
runBC' [] _ _ = failPCF $ "Error de ejecución: No hay instrucciones."
runBC' (PRINT : cs) e s@(I n : _) = do
    printPCF ("El resultado es "++(show n))
    runBC' cs e s
runBC' (PRINT : _) _ _ = failPCF $ "Error de ejecución: Solo se pueden imprimir naturales."
runBC' (STOP : _) _ _ = return ()
runBC' (CONST : n : cs) e s = runBC' cs e (I n : s)
runBC' (SUM : cs) e (I n2 : I n1 : ss) = runBC' cs e (I (n1+n2) : ss)
runBC' (PROD : cs) e (I n2 : I n1 : ss) = runBC' cs e (I (n1*n2) : ss)
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
runBC' (TAILCALL : cs) e (v : Fun ef cf : ss) = runBC' cf (v : ef) ss
runBC' _ _ _ = failPCF $ "Error de ejecución: Secuencia de instrucciones inválida."
