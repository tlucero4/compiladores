{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Main
Description : Compilador de PCF.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)
import Options.Applicative

--import Control.Monad
import Control.Monad.Trans
import Data.List (nub,  intersperse, isPrefixOf )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.IO ( stderr, hPutStr )
import qualified Data.Text.IO as TIO
import Data.Text.Lazy (toStrict)

import Global ( GlEnv(..) )
import Errors
import Lang
--import Parse ( P, tm, program, declOrTm, runP )
import Parse ( P, stm, sdecl, sprogram, sdeclOrSTm, runP )
import Elab ( elab, elab_sdecl, desugar, desugarTy, bc_elab_sdecl )
import CEK ( eval )
import PPrint ( pp , ppTy )
import MonadPCF
import TypeChecker ( tc, tcDecl )
import Optimizer ( optimize )
import Bytecompile
import Closure (runCC)
import CIR (runCanon)
import InstSel (codegen)
import LLVM.Pretty (ppllvm)

prompt :: String
prompt = "PCF> "

doOptimize :: Bool
doOptimize = True

----------------- SECCION BYTECODE

data Mode =   Interactive
            | Typecheck
            | Bytecompile
            | Canon
            | Run

-- | Parser de banderas
parseMode :: Parser Mode
parseMode = flag' Typecheck ( long "typecheck" <> short 't' <> help "Solo chequear tipos")
        <|> flag' Bytecompile (long "bytecompile" <> short 'b' <> help "Compilar a la BVM")
        <|> flag' Canon (long "canon" <> short 'c' <> help "Conversión a bajo nivel")
        <|> flag' Run (long "run" <> short 'r' <> help "Ejecutar bytecode en la BVM")
        <|> flag Interactive Interactive ( long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva" )

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode,[FilePath])
parseArgs = (,) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= go
    where opts = info (parseArgs <**> helper)
            ( fullDesc
            <> progDesc "Compilador de PCF"
            <> header "Compilador de PCF de la materia Compiladores 2020" )
    
go :: (Mode,[FilePath]) -> IO ()
go (Interactive,files) = do
    runPCF (runInputT defaultSettings (main' files))
    return ()
go (Typecheck, files) = do
    runPCF (bytecompileFiles files True)
    return ()
go (Bytecompile, files) = do
    runPCF (bytecompileFiles files False)
    return ()
go (Canon, files) = do
    runPCF (ccFiles files)
    return ()
go (Run,files) = do
    runPCF (byterunFiles files)
    return ()

showL :: Show a => (MonadPCF m, MonadMask m) => [a] -> m ()
showL [] = return ()
showL (x:xs) = do printPCF (show x)
                  showL xs
                  
showPP :: (MonadPCF m, MonadMask m) => [TDecl Term] -> m ()
showPP [] = return ()
showPP ((TDecl _ n _ d):xs) = do printPCF (n++": "++pp d)
                                 showPP xs
    
ccFiles :: (MonadPCF m, MonadMask m) => [String] -> m ()
ccFiles [] = return ()
ccFiles (x:xs) = do
        catchErrors $ ccFile x
        ccFiles xs
    
ccFile ::  (MonadPCF m, MonadMask m) => String -> m ()
ccFile f = do
    printPCF ("Abriendo "++f++"...")
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStr stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err ++"\n")
                         return "")
    case runP sprogram x filename of
         Left e -> printPCF ("Error de parseo: "++ show e)
         Right sdecls -> do printPCF "Archivo parseado"
                            decls <- bc_elab_sdecl sdecls
                            printPCF "Sintactic Sugar eliminada"
                            mapM_ tcDecl decls
                            printPCF "\n\n------------- DECLS:\n"
                            showPP decls
                            let odecls = if doOptimize
                                            then optimize decls
                                            else decls
                            printPCF "\n\n------------- OPTIMIZED:\n"
                            showPP odecls
                            let irdecls = runCC odecls 0
                            --printPCF "\n\n------------- IRDECLS:\n"
                            --showL irdecls
                            let canon = runCanon irdecls
                                llvm = toStrict $ ppllvm $ codegen canon
                            --printPCF "\n\n------------- CANON:\n"
                            --printPCF $ show canon
                            liftIO $ TIO.writeFile (f++".ll") llvm
                            printPCF ("Archivo "++f++".ll creado.\n")
                            return ()
    
bytecompileFiles :: (MonadPCF m, MonadMask m) => [String] -> Bool -> m ()
bytecompileFiles [] _       = return ()
bytecompileFiles (x:xs) jtc = do
        modify (\s -> s { lfile = x, inter = False })
        catchErrors $ bytecompileFile x jtc
        bytecompileFiles xs jtc

bytecompileFile ::  (MonadPCF m, MonadMask m) => String -> Bool -> m ()
bytecompileFile f jtc = do
    printPCF ("Abriendo "++f++"...")
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStr stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err ++"\n")
                         return "")
    sdecls <- parseIO filename sprogram x
    decls <- bc_elab_sdecl sdecls -- hacemos un desugaring a cada declaracion de la lista
    mapM_ tcDecl decls
    if jtc then do
            printPCF ("Las declaraciones de "++f++" están bien tipadas.")
           else do
            bytecode <- bytecompileModule decls -- transformamos la lista en un bytecode
            liftIO $ bcWrite bytecode (f++".byte") -- escribimos el archivo
            printPCF ("Archivo "++f++".byte creado.\n")
    
byterunFiles :: (MonadPCF m, MonadMask m) => [String] -> m ()
byterunFiles [] = return ()
byterunFiles (x:xs) = do
        printPCF ("Ejectutando "++x++"...")
        modify (\s -> s { lfile = x, inter = False })
        bytecode <- liftIO $ bcRead x
        catchErrors $ runBC bytecode
        byterunFiles xs

----------------- FIN SECCION BYTECODE
          
main' :: (MonadPCF m, MonadMask m) => [String] -> InputT m ()
main' args = do
        lift $ catchErrors $ compileFiles args
        s <- lift $ get
        when (inter s) $ liftIO $ putStrLn
          (  "Entorno interactivo para PCF0.\n"
          ++ "Escriba :? para recibir ayuda.")
        loop  
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand c
                       maybe loop (flip when loop) b
                       
compileFiles ::  MonadPCF m => [String] -> m ()
compileFiles []     = return ()
compileFiles (x:xs) = do
        modify (\s -> s { lfile = x, inter = False })
        compileFile x
        compileFiles xs

compileFile ::  MonadPCF m => String -> m ()
compileFile f = do
    printPCF ("Abriendo "++f++"...")
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStr stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err ++"\n")
                         return "")
    decls <- parseIO filename sprogram x
    mapM_ handleSDecl decls

parseIO ::  MonadPCF m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r
{-
handleDecl ::  MonadPCF m => Decl NTerm -> m ()
handleDecl (Decl p x t) = do
        let tt = elab t
        tcDecl (Decl p x tt)    
        te <- eval tt
        addDecl (Decl p x te)
        -}

handleSDecl :: MonadPCF m => SDecl STerm -> m ()
handleSDecl (SType p n t) = do ns <- lookupNTy n
                               case ns of
                                    Just _  -> failPosPCF p $ "El tipo "++n++" ya existe."
                                    Nothing -> do   dt <- desugarTy t
                                                    addNTy n dt
handleSDecl sd = do
                    d <- elab_sdecl sd
                    let (TDecl p x xty t) = d
                    tcDecl (TDecl p x xty t)
                    te <- eval t
                    addDecl (Decl p x te)

data Command = Compile CompileForm
             | Print String
             | PrintD String
             | Type String
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if isPrefixOf ":" x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   concat (intersperse ", " [ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   Main.Print     "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":dprint"]      "<exp>"   PrintD         "Imprime una declaración y sus ASTs",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = concat (intersperse ", " (map (++ if null a then "" else " " ++ a) c))
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand ::  MonadPCF m => Command  -> m Bool
handleCommand cmd = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printPCF (helpTxt commands) >> return True
       Browse ->  do  printPCF (unlines [ name | name <- reverse (nub (map declName glb)) ])
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase e
                          CompileFile f        -> put (s {lfile=f}) >> compileFile f
                      return True
       Main.Print e   -> printPhrase e >> return True
       PrintD d  -> printDecl d >> return True
       Type e    -> typeCheckPhrase e >> return True

compilePhrase ::  MonadPCF m => String -> m ()
compilePhrase x =
  do
    dot <- parseIO "<interactive>" sdeclOrSTm x
    case dot of 
      Left d  -> handleSDecl d
      Right t -> handleSTerm t
      
--handleTerm ::  MonadPCF m => NTerm -> m ()
handleSTerm ::  MonadPCF m => STerm -> m ()
handleSTerm t = do
         tt <- elab t
         s <- get
         ty <- tc tt (tyEnv s)
         te <- eval tt
         printPCF (pp te ++ " : " ++ ppTy ty)

printPhrase   :: MonadPCF m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" stm x
    ex <- elab x'
    dx <- desugar x'
    t  <- case dx of 
           (V p f) -> maybe ex id <$> lookupDecl f
           _        -> return ex  
    printPCF "STerm:"
    printPCF (show x')
    printPCF "\nTerm:"
    printPCF (show t)

printDecl   :: MonadPCF m => String -> m ()
printDecl x =
  do
    x' <- parseIO "<interactive>" sdecl x
    dx <- elab_sdecl x'
    printPCF "SDecl:"
    printPCF (show x')
    printPCF "\nDecl:"
    printPCF (show dx)

typeCheckPhrase :: MonadPCF m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" stm x
         tt <- elab t
         s <- get
         ty <- tc tt (tyEnv s)
         printPCF (ppTy ty)
