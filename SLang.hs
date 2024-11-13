module SLang ( NamedLam ) where

import Data.Text ( unpack )

import Prettyprinter.Render.Terminal
  ( renderStrict, italicized, color, colorDull, bold, Color (..), AnsiStyle )
import Prettyprinter
    ( (<+>),
      annotate,
      defaultLayoutOptions,
      layoutSmart,
      nest,
      sep,
      parens,
      line,
      Doc,
      Pretty(pretty) )

type Name = String

infixl `NApp`
data NamedLam = Var Name | NLam [Name] NamedLam | NApp NamedLam NamedLam

instance Show NamedLam where
  show = ppNamedLam

symbolColor :: Doc AnsiStyle -> Doc AnsiStyle
symbolColor = annotate bold

binderColor :: Doc AnsiStyle -> Doc AnsiStyle
binderColor = annotate bold

parenIf :: Bool -> Doc a -> Doc a
parenIf p = if p then parens else id

collectApp :: NamedLam -> (NamedLam, [NamedLam])
collectApp = go [] where
  go ts (NApp h tt) = go (tt:ts) h
  go ts h = (h, ts)

t2doc :: Bool -> NamedLam -> Doc AnsiStyle
t2doc at (Var x) = pretty x
t2doc at (NLam xs t) =
  parenIf at $
    symbolColor (pretty "\\")
    <> sep (map (binderColor . pretty) xs)
    <> symbolColor (pretty ".")
    <+> nest 2 (t2doc False t)
t2doc at t@(NApp _ _) =
  let (h, ts) = collectApp t
  in  parenIf at $
        t2doc True h <+> sep (map (t2doc True) ts)

render :: Doc AnsiStyle -> String
render = unpack . renderStrict . layoutSmart defaultLayoutOptions

ppNamedLam :: NamedLam -> String
ppNamedLam = render . t2doc False