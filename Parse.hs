module Parse where


import Text.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.Parsec.Token as Tok

type P = Parsec String ()

{-
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

langDef :: LanguageDef u
langDef = emptyDef

parens :: P a -> P a
parens = Tok.parens lexer

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

identifier :: P String
identifier = Tok.identifier lexer

symbol :: String -> P String
symbol = Tok.symbol lexer

name :: P Name
name = identifier

var :: P NamedLam
var = Var <$> name

lam :: P NamedLam
lam = do  symbol "\\"
          xs <- many1 name
          symbol "."
          NLam xs <$> term

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