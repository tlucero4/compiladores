{-|
Module      : Global
Description : Define el estado global del compilador
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}
module Global where

import Lang

data GlEnv = GlEnv {
  inter :: Bool,        --  ^ True, si estamos en modo interactivo.
  lfile :: String,      -- ^ Último archivo cargado.
  glb :: [Decl Term],   -- ^ Entorno con declaraciones globales
  tyEnv :: [(Name,Ty)]  -- ^ Entorno de tipado de declaraciones globales
  namedTy :: [(Name,Ty)]-- ^ Entorno de sinonimos de tipos
}

-- | Valor del estado inicial
initialEnv :: GlEnv
initialEnv = GlEnv True "" [] [] []


-- TIPOS:
-- creamos el entorno namedTy :: [(Name,Ty)]
-- creamos un parse para SNamedTypes que devuelve un NamedTy Name Ty
-- este parser será una posibilidad mas en sdeclOrSTm
-- que sera llevado a otro caso para compilePhrase en Main
-- y resultara en una funcion handleSNAmedTy que lo agregara al nuevo entorno
-- en tyatom (Parse) debemos crear una manera de reconocer estos nuevos tipos y devolver un UntrackedTy Name
-- hacemos un desugar de tipos donde se transforma un UntrackedTy por su NamedTy correspondiente si aparece en el entorno, o falla sino
-- en el TypeChecker, debemos considerar que cuando aparece algo con termino NamedTy, solo debemos quedarnos con su Ty interno
-- que hacer con respecto a la impresion? por ejemplo para errores
