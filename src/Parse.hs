{-|
Module      : Parse
Description : Define un parser de términos PCF0 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (stm, tm, Parse.parse, decl, sdecl, runP, P, sprogram, program, sdeclOrSTm, declOrTm) where

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
                          "succ", "pred", "ifz", "Nat"],
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

tyatom :: P Ty
tyatom = (reserved "Nat" >> return NatTy)
         <|> parens typeP

typeP :: P Ty
typeP = try (do 
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (FunTy x y))
      <|> tyatom
          
const :: P Const
const = CNat <$> num

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

binding :: P (Name, Ty)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return (v, ty)

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
            

-- Sección para parsear azucar sintactica:

sconst :: P Const
sconst = CNat <$> num

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

satom :: P STerm
satom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens stm

--para parsear una lista de binders
binders :: P [(Name, Ty)]
binders = many1 (parens $ do 
                    v <- var
                    reservedOp ":"
                    ty <- typeP 
                    return (v,ty))
         
slam :: P STerm
slam = do i <- getPos
          reserved "fun"
          vts <- binders
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
     v <- var
     reservedOp ":"
     ty <- typeP
     reservedOp "="
     std <- stm
     reserved "in"
     sta <- stm
     return (SLet i v ty std sta)
     
sletFun :: P STerm
sletFun = do 
        i <- getPos
        reserved "let"
        n <- var
        vts <- binders
        reservedOp ":"
        ty <- typeP
        reservedOp "="
        std <- stm
        reserved "in"
        sta <- stm
        return (SLetFun i n ty vts std sta)

sletFunRec :: P STerm
sletFunRec = do 
            i <- getPos
            reserved "let"
            reserved "rec"
            n <- var
            vts <- binders
            reservedOp ":"
            ty <- typeP
            reservedOp "="
            std <- stm
            reserved "in"
            sta <- stm
            return (SLetFunRec i n ty vts std sta)

-- | Parser de términos azucarados
stm :: P STerm -- falta agregar sletFunRec
stm = sunaryOp <|> satom <|> slam <|> sapp <|> sifz <|> sfix <|> (try sletFun <|> slet)

-- | Parser de declaraciones azucaradas
sdeclt :: P (SDecl STerm)
sdeclt = do 
     i <- getPos
     reserved "let"
     v <- var
     reservedOp ":"
     ty <- typeP
     reservedOp "="
     t <- stm
     return (SDecl i v ty [] False t)
     
-- | Parser de declaraciones de funciones azucaradas
sdeclf :: P (SDecl STerm)
sdeclf = do i <- getPos
            reserved "let"
            f <- var
            nts <- binders
            reservedOp ":"
            fty <- typeP
            reservedOp "="
            t <- stm
            return (SDecl i f fty nts False t)
     
sdeclfr :: P (SDecl STerm)
sdeclfr = do i <- getPos
             reserved "let"
             reserved "rec"
             f <- var
             nts <- binders
             reservedOp ":"
             fty <- typeP
             reservedOp "="
             t <- stm
             return (SDecl i f fty nts True t)

sdecl :: P (SDecl STerm)
sdecl = try sdeclfr <|> sdeclf <|> sdeclt

-- | Parser de programas con azucar sintactico (listas de declaraciones) 
sprogram :: P [SDecl STerm]
sprogram = many sdecl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
sdeclOrSTm :: P (Either (SDecl STerm) STerm)
sdeclOrSTm =  try (Left <$> sdecl) <|> (Right <$> stm)

sparse :: String -> STerm
sparse s = case runP stm s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
