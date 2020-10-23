{-|
Module      : Parse
Description : Define un parser de términos PCF0 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (stm, Parse.sparse, sdecl, runP, P, sprogram, sdeclOrSTm) where

import Prelude hiding ( const )
import Lang
import Common
import Text.Parsec hiding (runP)
import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language ( GenLanguageDef(..), emptyDef )

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser $
        emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "fun", "fix", "then", "else",
                          "rec", "type", "in",
                          "succ", "pred", "ifz", "Nat",
                          "sum", "sub"],
         reservedOpNames = ["->",":","="]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer 
natural = Tok.natural lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier 

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)
          
const :: P Const
const = CNat <$> num
{-
unaryOp :: P NTerm
unaryOp = do
  i <- getPos
  foldr (\(w, r) rest -> try (do 
                                 reserved w
                                 a <- atom
                                 return (r a)) <|> rest) parserZero (mapping i)
  where
   mapping i = [
       ("succ", UnaryOp i Succ)
     , ("pred", UnaryOp i Pred)
    ]

atom :: P NTerm
atom =     (flip Const <$> const <*> getPos)
       <|> flip V <$> var <*> getPos
       <|> parens tm

lam :: P NTerm
lam = do i <- getPos
         reserved "fun"
         (v,ty) <- parens $ do 
                    v <- var
                    reservedOp ":"
                    ty <- typeP 
                    return (v,ty)
         reservedOp "->"
         t <- tm
         return (Lam i v ty t)

-- Nota el parser app también parsea un solo atom.
app :: P NTerm
app = (do i <- getPos
          f <- atom
          args <- many atom
          return (foldl (App i) f args))

ifz :: P NTerm
ifz = do i <- getPos
         reserved "ifz"
         c <- tm
         reserved "then"
         t <- tm
         reserved "else"
         e <- tm
         return (IfZ i c t e)

fix :: P NTerm
fix = do i <- getPos
         reserved "fix"
         (f, fty) <- parens binding
         (x, xty) <- parens binding
         reservedOp "->"
         t <- tm
         return (Fix i f fty x xty t)

-- | Parser de términos
tm :: P NTerm
tm = app <|> lam <|> ifz <|> unaryOp <|> fix

-- | Parser de declaraciones
decl :: P (Decl NTerm)
decl = do 
     i <- getPos
     reserved "let"
     v <- var
     reservedOp "="
     t <- tm
     return (Decl i v t)

-- | Parser de programas (listas de declaraciones) 
program :: P [Decl NTerm]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either (Decl NTerm) NTerm)
declOrTm =  try (Left <$> decl) <|> (Right <$> tm)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> NTerm
parse s = case runP tm s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
            
            -}

-- Sección para parsear azucar sintactica:

binding :: P (Name, STy)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return (v, ty)
             
tyatom :: P STy
tyatom = (reserved "Nat" >> return SNatTy)
         <|> parens typeP
         <|> (do
                i <- getPos
                st <- identifier
                return (SNamedTy i st))

typeP :: P STy
typeP = try (do 
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (SFunTy x y))
      <|> tyatom
      
sconst :: P Const
sconst = CNat <$> num

-- esta implementacion queda desestimada
{-
sunaryOp :: P STerm
sunaryOp = do
  i <- getPos
  foldr (\(w, r) rest -> try (do 
                                 reserved w
                                 a <- satom
                                 return (r a)) <|> rest) parserZero (mapping i)
  where
   mapping i = [
       ("succ", SUnaryOp i Succ)
     , ("pred", SUnaryOp i Pred)
    ]
    -}

    -- ¿como hacemos para que en elab se diferencie entre un sunaryOp sin aplicacion con uno al que le sigue un termino?
    -- ¿se podría usando sapp? ¿habria que ver en el desugar de SApp si hay un pred seguido de un termino?
unaryOpName :: P UnaryOp
unaryOpName =
      (reserved "succ" >> return Succ)
  <|> (reserved "pred" >> return Pred)
  
binaryOpName :: P BinaryOp
binaryOpName =
      (reserved "sum" >> return Sum)
  <|> (reserved "sub" >> return Sub)
  
tyvar :: P Name
tyvar = Tok.lexeme lexer $ do
 c  <- upper
 cs <- option "" identifier
 return (c:cs)


sunaryOp :: P STerm
sunaryOp = do
             i <- getPos
             o <- unaryOpName
             return (SUnaryOp i o)
             
sbinaryOp :: P STerm
sbinaryOp = do
             i <- getPos
             b <- binaryOpName
             return (SBinaryOp i b)

satom :: P STerm
satom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> sbinaryOp
       <|> sunaryOp
       <|> parens stm

--para parsear una lista de binders
binders :: P [[(Name, STy)]]
binders = many (parens $ do 
                    vs <- many1 var
                    reservedOp ":"
                    ty <- typeP
                    return (map (\n -> (n, ty)) vs))
         
slam :: P STerm
slam = do i <- getPos
          reserved "fun"
          vts' <- binders
          let vts = concat vts'
          reservedOp "->"
          t <- stm
          return (SLam i vts t)

sapp :: P STerm
sapp = (do i <- getPos
           f <- satom
           args <- many satom
           return (foldl (SApp i) f args))

sifz :: P STerm
sifz = do i <- getPos
          reserved "ifz"
          c <- stm
          reserved "then"
          t <- stm
          reserved "else"
          e <- stm
          return (SIfZ i c t e)
{-
sfix :: P STerm
sfix = do i <- getPos
          reserved "fix"
          nts <- binders
          reservedOp "->"
          t <- stm
          return (SFix i nts t)
          -}
sfix :: P STerm
sfix = do i <- getPos
          reserved "fix"
          (f, fty) <- parens binding
          (x, xty) <- parens binding
          reservedOp "->"
          t <- stm
          return (SFix i f fty x xty t)   

slet :: P STerm
slet = do 
     i <- getPos
     reserved "let"
-- la idea es que si puede consumir la palabra 'rec' devuelva true, y si "falla" devuelva false:
     r <- ((do
            reserved "rec"
            return True) <|> return False)
     n <- var
     vts' <- binders
     let vts = concat vts'
     reservedOp ":"
     ty <- typeP
     reservedOp "="
     std <- stm
     reserved "in"
     sta <- stm
     return (SLet i n ty vts r std sta)

-- | Parser de términos azucarados
stm :: P STerm
stm = sapp <|> slet <|> slam <|> sifz <|> sfix

-- | Parser de declaraciones azucaradas
sdecll :: P (SDecl STerm)
sdecll = do i <- getPos
            reserved "let"
            r <- ((do
                     reserved "rec"
                     return True) <|> return False)
            f <- var
            nts' <- binders
            let nts = concat nts'
            reservedOp ":"
            fty <- typeP
            reservedOp "="
            t <- stm
            return (SDecl i f fty nts r t)

sdeclt :: P (SDecl STerm)
sdeclt = do i <- getPos
            reserved "type"
            st <- tyvar
            reservedOp "="
            rt <- typeP
            return (SType i st rt)

sdecl :: P (SDecl STerm)
sdecl = sdecll <|> sdeclt
        
-- | Parser de programas con azucar sintactico (listas de declaraciones) 
sprogram :: P [SDecl STerm]
sprogram = many sdecl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
sdeclOrSTm :: P (Either (SDecl STerm) STerm)
sdeclOrSTm =  try (Right <$> stm) <|> (Left <$> sdecl)

runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

sparse :: String -> STerm
sparse s = case runP stm s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
