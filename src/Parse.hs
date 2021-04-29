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
                          "rec", "type", "in", "print",
                          "succ", "pred", "ifz", "Nat",
                          "add", "sub","mult"],
         reservedOpNames = ["->",":","=","+","-","*"]
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

unaryOpName :: P UnaryOp
unaryOpName =
      (reserved "succ" >> return Succ)
  <|> (reserved "pred" >> return Pred)
  <|> (reserved "print" >> return Print)
  
binaryOpName :: P BinaryOp
binaryOpName =
      (reserved "add" >> return Add)
  <|> (reserved "sub" >> return Sub)
  <|> (reserved "mult" >> return Prod)

infixBinaryOpName :: P BinaryOp
infixBinaryOpName =
      (reserved "+" >> return Add)
  <|> (reserved "-" >> return Sub)
  <|> (reserved "*" >> return Prod)

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
             
infixBinaryOp :: P STerm
infixBinaryOp = do i <- getPos
                   o <- infixBinaryOpName
                   t <- stm
                   return (SInfixBinaryOp i o t)

sbinaryOp :: P STerm
sbinaryOp = do
             i <- getPos
             b <- binaryOpName
             return (SBinaryOp i b)

satom :: P STerm
satom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> infixBinaryOp
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
