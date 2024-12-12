module Parse where

-- MAYBE usar indentacion

import Lang hiding ( var )

import Text.Parsec hiding ( runP )
import Text.ParserCombinators.Parsec.Language
import qualified Text.Parsec.Token as Tok
import Control.Monad.Identity (Identity)
import Control.Exception.Extra (tryBool)

type P = Parsec String ()

-- NICETOHAVE parsear, por ej, un punto pegado a una barra

langDef :: LanguageDef u
langDef = emptyDef {
  commentStart = "/*",
  commentEnd = "*/",
  commentLine = "//",
  reservedNames = ["let", "rec", "λ", "\\", "fix", "in", "data", "elim",
                    "Set", "Nat", "suc", "zero", "refl"],
  reservedOpNames = ["->", "→", ":", ":=", "≔", "=", "."]
}

lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

parens :: P a -> P a
parens = Tok.parens lexer

braces :: P a -> P a
braces = Tok.braces lexer

semiSep :: P a -> P [a]
semiSep = Tok.semiSep lexer

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

szero :: P STerm
szero = reserved "zero" >> return SZero

ssuc :: P STerm
ssuc = reserved "suc" >> return SSuc

srefl :: P STerm
srefl = reserved "refl" >> return SRefl

spi :: P STerm
spi = do
  a <- arg
  reservedOp "->" <|> reservedOp "→"
  ty <- stype
  return (SPi a ty)

sort :: P STerm
sort = try set <|> set0 
  where
    set = do
      reserved "Set"
      n <- num
      return (SSort (Set n))
    set0 = do
      reserved "Set"
      return (SSort (Set 0))

arg :: P SArg
arg = parens arg' <|> arg'
  where
    arg' = do
      x <- name
      reservedOp ":"
      ty <- stype
      return (Arg x ty)

atom :: P STerm
atom =
  lit 
  <|> var
  <|> snat
  <|> szero
  <|> ssuc
  <|> srefl
  <|> try spi
  <|> sort
  <|> parens sterm

lam :: P STerm
lam = do  reserved "\\" <|> reserved "λ"
          a <- arg
          symbol "."
          SLam a <$> sterm

fix :: P STerm
fix = do
  reserved "fix"
  f <- name
  a <- parens arg
  reservedOp ":"
  ty <- stype
  reservedOp "."
  t <- sterm
  return (SFix f a ty t)

elim :: P STerm
elim = do
  reserved "elim"
  t <- sterm
  bs <- braces (semiSep branch)
  return (SElim t bs)

branch :: P SElimBranch
branch = do
  c <- name <|> choice (map reservedName cons)
  as <- many name
  reservedOp ":=" <|> reservedOp "≔"
  t <- sterm
  return (ElimBranch c as t)
  where
    reservedName n = reserved n >> return n 
    cons = ["zero", "suc", "refl"]

app :: P STerm
app = do
  f <- atom
  args <- many atom
  return (foldl SApp f args)

expr :: P STerm
expr = app <|> lam <|> fix <|> elim


equalOp :: STerm -> P STerm
equalOp t = do
  reservedOp "="
  u <- expr
  return (SEq t u)

ann :: STerm -> P STerm
ann t = do
  reservedOp ":"
  ty <- stype
  return (SAnn t ty)

sterm :: P STerm
sterm = do
  t <- expr
  ann t <|> equalOp t <|> return t


stype :: P SType
stype = Type <$> sterm

parse :: String -> STerm
parse s = case runP sterm s "" of
            Right t -> t
            Left e -> error $ show e

runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s
