{-|
Module      : Optimizer
Description : Define algunas optimizaciones de expresiones

Este módulo implementa algunas optimizaciones vistas en clase (simplificaciones aritméticas, eliminación
de código muerto, y expansiones inline de funciones no recursivas).
-}

module Optimizer (
   optimize
   ) where

import Lang
import Common (Pos(NoPos))
import Subst (closeN, substN)
import MonadPCF
import Control.Monad.State.Lazy
import Control.Monad.Writer.Lazy

-- Definimos algunas variables de la optimización

numCycles :: Int
numCycles = 3

inlineHeur :: Int
inlineHeur = 100

-- | 'apply2Term' aplica la función dada sobre
-- una declaración en el cuerpo de ésta
apply2Term :: (Term -> Term) -> TDecl Term -> TDecl Term
apply2Term f (TDecl p n t b) = TDecl p n t $ f b

-- | 'optimize' ejecuta ciclicamente (hasta un valor dado)
-- la reducción de expresiones aritmeticas seguidas del inline
optimize :: [TDecl Term] -> [TDecl Term]
optimize = doCycle numCycles where                     
	doCycle 0 ts = ts
	doCycle n ts = doCycle (n-1) $ inlineFuns $ map (apply2Term arithCalc) ts
                        

-- Reducción de expresiones aritméticas y eliminación de código muerto

-- | 'arithCalc' se encarga de la reducción sobre operaciones binarios
-- y también elimina código muerto en los condicionales
arithCalc :: Term -> Term
arithCalc (Lam i n ty t) = Lam i n ty (arithCalc t)
arithCalc (App i t u) = App i (arithCalc t) (arithCalc u)
arithCalc (Fix i f fty n nty t) = Fix i f fty n nty (arithCalc t)
arithCalc (IfZ i c t e) = case c of -- DCE
                               Const _ (CNat 0) -> (arithCalc t)
                               Const _ (CNat n) -> (arithCalc e)
                               _ -> IfZ i (arithCalc c) (arithCalc t) (arithCalc e)
arithCalc (Let i n ty d t) = Let i n ty (arithCalc d) (arithCalc t)
arithCalc (UnaryOp i o t) = UnaryOp i o (arithCalc t)
arithCalc (BinaryOp i o t u) = let t' = arithCalc t
                                   u' = arithCalc u
                               in case (t', u') of
                                    (Const i (CNat n), Const _ (CNat m)) -> case o of
                                                                                 Add -> Const i (CNat $ n + m)
                                                                                 Sub -> if (n > m) then Const i (CNat $ n - m) else Const i (CNat 0)
                                                                                 Prod -> if (n == 0 || m == 0) then Const i (CNat 0) else Const i (CNat $ n * m)
                                    _                                    -> BinaryOp i o t' u'
arithCalc t = t

-- Funciones Inline (solo para funciones no recursivas)

-- | 'getFreshName' devuelve siempre un nombre fresco
getFreshName :: Name -> State Int Name
getFreshName n = do i <- get
                    modify (+1)
                    return ("_" ++ n ++ show i)

-- | 'addLets' es una función auxiliar que simplemente agrega let-binders
-- al cuerpo del término expandido para que los argumentos complejos queden
-- correctametne bindeados a su Let correspondiente.
addLets :: [(Name, Term,Ty)] -> Term ->  Term
addLets [] t = t
addLets ((n,c,ty):ns) t = addLets ns $ Let NoPos n ty c t
                    
-- | 'substLamR' toma
-- @ un contador de argumentos ascendente
-- @ un contador de argumentos decreciente
-- @ una lista con la tupla (nombre, cuerpo, tipo) para guardar argumentos complejos
-- @ una lista de cuerpos de argumentos
-- @ el cuerpo de la función a expandir
-- La idea es eliminar todos los binders del cuerpo de la funcion, chequeando el tipo de argumento que le corresponde.
-- Si el argumento es un valor, se deja en la lista de cuerpos de argumentos tal cual esta.
-- Si el argumento es complejo, se reemplaza por un nombre fresco y se guarda en la lista de argumentos complejo su nombre fresco y su cuerpo
-- Una vez procesados todos los argumentos, primero se sustituyen todos los cuerpos de los argumentos en el cuerpo de la función
-- desprovisto de binders. Luego, para aquellos cuerpos que se reemplazaron por un nombre fresco, los traducimos nuevamente a indices
-- de Bruijn para que luego agregando los lets-binders queden correctamente bindeados.
substLamR :: Int -> Int -> [(Name, Term, Ty)] -> [Term] ->  Term -> State Int Term
substLamR _ 0 ns as t = return $ addLets ns $ closeN (reverse $ map (\(x,_,_) -> x) ns) $ substN as t
substLamR k j ns as (Lam _ _ ty t) = case (as !! k) of
                                        V _ _ -> substLamR (k+1) (j-1) ns as t
                                        Const _ _ -> substLamR (k+1) (j-1) ns as t
                                        c ->  do fr <- getFreshName "lv"
                                                 let as' = let (as1,as2) = splitAt k as
                                                            in (as1 ++ [V NoPos (Free fr)] ++ tail as2)
                                                 substLamR (k+1) (j-1) ((fr,c,ty):ns) as' t

-- | 'getArgs' se encarga de devolver una lista de argumentos
-- solo cuando se aplican sobre la funcion correspondiente
-- y con el mismo numero de argumentos que espera la función 
getArgs :: Term -> Name -> [Term] -> Maybe [Term]
getArgs (App _ t a) n as = getArgs t n (a:as)
getArgs (V _ (Free n')) n as = if (n == n') then Just as
                                            else Nothing
getArgs _ _ _ = Nothing

-- | 'replaceFun' toma un nombre de función, su cuerpo, y su número de argumentos,
-- y reemplaza todas las aplicaciones totales (no parciales) de la función por su cuerpo
replaceFun :: Name -> Term -> Int -> Term -> Term
replaceFun n r na x@(App i t a) = case (getArgs t n [a]) of
                                  Just as -> let as' = map (replaceFun n r na) as
											 in case r of
                                                  Lam _ _ _ _ -> fst $ runState (substLamR 0 (length as) [] as' r) 0
                                                  Fix _ _ _ _ _ t -> fst $ runState (substFixR (na - 1) [] (head as') (tail as') t) 0
                                                  _ -> App i (replaceFun n r na t) (replaceFun n r na a)
                                  Nothing -> App i (replaceFun n r na t) (replaceFun n r na a)
replaceFun n r na (Lam i x ty t) = Lam i x ty (replaceFun n r na t)
replaceFun n r na (Fix i f fty x xty t) = Fix i f fty x xty (replaceFun n r na t)
replaceFun n r na (IfZ i c t e) = IfZ i (replaceFun n r na c) (replaceFun n r na t) (replaceFun n r na e)
replaceFun n r na (Let i x ty d t) = Let i x ty (replaceFun n r na d) (replaceFun n r na t)
replaceFun n r na (UnaryOp i o t) = UnaryOp i o (replaceFun n r na t)
replaceFun n r na (BinaryOp i o t u) = BinaryOp i o (replaceFun n r na t) (replaceFun n r na u)
replaceFun _ _ _ t = t

-- | 'calcSizeOfFun' es la heuristica implementada, que calcula
-- el "tamaño" de la función dandole valores a los términos
calcSizeOfFun :: Term -> Int
calcSizeOfFun (Lam _ _ _ t) = 1 + calcSizeOfFun t
calcSizeOfFun (App _ t u) = 1 + calcSizeOfFun t + calcSizeOfFun u
calcSizeOfFun (Fix _ _ _ _ _ t) = 2 + calcSizeOfFun t
calcSizeOfFun (IfZ _ c t e) = calcSizeOfFun c + calcSizeOfFun t + calcSizeOfFun e
calcSizeOfFun (Let _ _ _ d t) = calcSizeOfFun d + calcSizeOfFun t
calcSizeOfFun (UnaryOp _ _ t) = calcSizeOfFun t
calcSizeOfFun (BinaryOp _ _ t u) = calcSizeOfFun t + calcSizeOfFun u
calcSizeOfFun t = 1

-- | 'calcSizeOfArgs' calcula el numero de composiciones de un tipo 
calcSizeOfArgs :: Ty -> Int
calcSizeOfArgs (FunTy _ t) = 1 + calcSizeOfArgs t
calcSizeOfArgs _ = 0

-- | 'getFuns' toma todas las funciones, las pasa por un filtro
-- de acuerdo con la heuristica elegida Y devuelve una tabla
getFuns :: [TDecl Term] -> Writer [(Name, Term, Int)] ()
getFuns [] = return ()
getFuns (x:xs) = case (tdeclBody x) of
                      Lam _ _ _ _ -> do let s = calcSizeOfFun (tdeclBody x)
                                            nargs = calcSizeOfArgs (tdeclType x)
                                        when (s < inlineHeur) $ tell [(tdeclName x, tdeclBody x, nargs)]
                                        getFuns xs  
                      Fix _ _ _ _ _ _ -> do let s = calcSizeOfFun (tdeclBody x)
                                                nargs = calcSizeOfArgs (tdeclType x)
                                            when (False) $ tell [(tdeclName x, tdeclBody x, nargs)] -- a las funciones recursivas no le hacemos inline
                                            getFuns xs  
                      _ -> getFuns xs

-- | 'deleteFun' elimina una función declarada luego de que fue
-- expandida en todas sus aplicaciones
deleteFun :: Name -> [TDecl Term] -> [TDecl Term]
deleteFun _ [] = []
deleteFun n (x:xs) | n == tdeclName x = xs
                   | otherwise        = x : (deleteFun n xs)

-- | 'doInline' pasa función por función el proceso de inline,
-- sobre un conjunto de declaraciones mas reducido (posiblemente)
doInline :: [TDecl Term] -> [(Name, Term, Int)] -> [TDecl Term]
doInline ts [] = ts
doInline ts ((n, t, na):xs) = let ts' = map (apply2Term (replaceFun n t na)) (deleteFun n ts)
                              in doInline ts' xs

-- | 'inlineFun' primero calcula una tabla de todas las funciones que
-- cumplen con la heuristica y luego las pasa por el inliner                    
inlineFuns :: [TDecl Term] -> [TDecl Term]
inlineFuns ts = let (_, table) = runWriter (getFuns ts)
                in doInline ts $ reverse table                  

-- El inline para funciones recursivas no funciona

-- | 'delAppFix' 
delAppFix :: Int -> Term -> Maybe Term
delAppFix k t@(App _ (V _ (Bound k')) u) = if (k + 1 == k') then Just t else Nothing
delAppFix k (App _ t u) = delAppFix k t
delAppFix _ _ = Nothing

-- | 'substFix' 
substFix :: Term -> Int -> Term -> Term
substFix r k (App i t u) = case delAppFix k t of
                                Just a -> substFix r k a
                                Nothing -> App i (substFix r k t) (substFix r k u)
substFix r k (Lam i x ty t) = Lam i x ty t
substFix r k (Fix i f fty x xty t) = Fix i f fty x xty t
substFix r k (IfZ i c t e) = IfZ i (substFix r k c) (substFix r k t) (substFix r k e)
substFix r k (Let i x ty d t) = Let i x ty (substFix r k d) (substFix r k t)
substFix r k (UnaryOp i o t) = UnaryOp i o (substFix r k t)
substFix r k (BinaryOp i o t u) = BinaryOp i o (substFix r k t) (substFix r k u)
substFix r k t@(V i (Bound n)) = if (n == k) then r else t
substFix _ _ t = t

-- | 'substFixR' 
substFixR :: Int -> [Name] -> Term -> [Term] -> Term -> State Int Term
substFixR k ns fa (a:as) (Lam _ _ _ t) = case a of
                                               V _ _ -> substFixR (k-1) ns fa as $ substFix a k t
                                               Const _ _ -> substFixR (k-1) ns fa as $ substFix a k t
                                               _ ->  do fr <- getFreshName "rv" 
                                                        let it = substFix (V NoPos (Free fr)) k t
                                                        ap <- substFixR (k-1) (fr:ns) fa as it
                                                        return (Let NoPos fr NatTy a ap)
substFixR k ns fa [] t = do fn <- getFreshName "prel"
                            fv <- getFreshName "var"
                            fr <- getFreshName "rv"
                            let (inT, ff) = case fa of
                                                V _ _ -> (App NoPos (V NoPos (Bound 0)) fa, "")
                                                Const _ _ -> (App NoPos (V NoPos (Bound 0)) fa, "")
                                                _ -> (App NoPos (V NoPos (Bound 0)) (V NoPos (Free fr)), fr)
                                letT = Fix NoPos fn NatTy fv NatTy t
                            return $ if null ff then closeN (reverse ns) (Let NoPos fn NatTy letT inT)
                                                else Let NoPos ff NatTy fa $ closeN (ff:reverse ns) (Let NoPos fn NatTy letT inT)
