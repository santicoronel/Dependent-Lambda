module Parse where

-- TODO Pi, Sort, equal


import Lang hiding ( var )

import Text.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.Parsec.Token as Tok
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)

type P = Parsec String ()

langDef :: LanguageDef u
langDef = emptyDef {
  commentStart = "/*",
  commentEnd = "*/",
  commentLine = "//",
  reservedNames = ["let", "rec", "λ", "\\", "fix", "in", "data", "elim",
                    "Set", "Nat"],
  reservedOpNames = ["->", "→", ":", ":=", "=", "."]
}

lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

parens :: P a -> P a
parens = Tok.parens lexer

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

identifier :: P String
identifier = Tok.identifier lexer

symbol :: String -> P String
symbol = Tok.symbol lexer

natural :: P Integer
natural = Tok.natural lexer

-------------------------------------------------------------

num :: P Int
num = fromInteger <$> natural

name :: P Name
name = identifier

lit :: P STerm
lit = Lit <$> num

var :: P STerm
var = SV <$> name

snat :: P STerm
snat = reserved "Nat" >> return SNat

spi :: P STerm
spi = do
  a <- arg
  reservedOp "->" <|> reservedOp "→"
  ty <- stype
  return (SPi a ty)

sort :: P STerm
sort = do
  reserved "Set"
  n <- num
  return (SSort (Set n))

arg :: P SArg
arg = parens arg' <|> arg'
  where
    arg' = do
      x <- name
      reservedOp ":"
      ty <- stype
      return (Arg x ty)

atom :: P STerm
atom = lit <|> var <|> snat <|> spi <|> sort <|> parens expr

lam :: P STerm
lam = do  reserved "\\" <|> reserved "λ"
          a <- arg
          symbol "."
          SLam a <$> expr

fix :: P STerm
fix = do
  reserved "fix"
  f <- name
  a <- parens arg
  reservedOp ":"
  ty <- stype
  reservedOp "."
  t <- expr
  return (SFix f a ty t)

app :: P STerm
app = do
  f <- atom
  args <- many atom
  return (foldl SApp f args)

equalOp :: Operator String () Identity STerm
equalOp = Ex.Infix (reservedOp "=" >> return SEq ) Ex.AssocNone

table :: [[Operator String () Identity STerm]]
table = [[equalOp]]

expr :: P STerm
expr = Ex.buildExpressionParser table sterm

sterm :: P STerm
sterm = app <|> lam <|> fix

stype :: P SType
stype = Type <$> expr

{-
atom :: P NamedLam
atom = var <|> lam <|> parens app

app :: P NamedLam
app = do  f <- atom
          args <- many atom
          return (foldl NApp f args)

term :: P NamedLam
term = app

parseLam :: P NamedLam
parseLam = term

runpLam :: String -> NamedLam
runpLam s = case runParser (whiteSpace *> term <* eof) () "" s of
              Right t -> t
              Left e -> error $ show e
          
-}

