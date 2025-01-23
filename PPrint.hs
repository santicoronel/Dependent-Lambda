module PPrint where

import Lang

import Data.Text ( unpack )
import Prettyprinter.Render.Terminal
  ( renderStrict, italicized, color, colorDull, Color (..), AnsiStyle )
import Prettyprinter
    ( (<+>),
      annotate,
      defaultLayoutOptions,
      layoutSmart,
      nest,
      sep,
      parens,
      braces,
      line,
      lbrace,
      rbrace,
      dot,
      colon,
      semi,
      vsep,
      Doc,
      Pretty(pretty), punctuate)

--Colores
constColor :: Doc AnsiStyle -> Doc AnsiStyle
constColor = annotate (color Red)
opColor :: Doc AnsiStyle -> Doc AnsiStyle
opColor = annotate (color Green)
keywordColor :: Doc AnsiStyle -> Doc AnsiStyle
keywordColor = annotate (color Blue)
typeColor :: Doc AnsiStyle -> Doc AnsiStyle
typeColor = annotate (color Blue <> italicized)
typeOpColor :: Doc AnsiStyle -> Doc AnsiStyle
typeOpColor = annotate (colorDull Blue)
defColor :: Doc AnsiStyle -> Doc AnsiStyle
defColor = annotate (colorDull Magenta <> italicized)
nameColor :: Doc AnsiStyle -> Doc AnsiStyle
nameColor = id

-- | Pretty printer de nombres (Doc)
name2doc :: Name -> Doc AnsiStyle
name2doc n = nameColor (pretty n)

-- |  Pretty printer de nombres (String)
ppName :: Name -> String
ppName = id

parenIf :: Bool -> Doc a -> Doc a
parenIf True = parens
parenIf _ = id

collectApp :: STerm -> (STerm, [STerm])
collectApp = go []
  where
    go as (SApp t u) = go (u : as) t
    go as f = (f, as)

collectPi :: STerm -> [Doc AnsiStyle]
collectPi (SPi arg ty) = 
  (arg2doc arg <+> opColor (pretty "->")) : collectPi (unType ty)
collectPi ty = [t2doc False ty]

arg2doc :: SArg -> Doc AnsiStyle
arg2doc (Arg xs ty) =
  parens $
  sep (map name2doc xs ++ [opColor colon, ty2doc False ty])

ty2doc :: Bool -> SType -> Doc AnsiStyle
ty2doc at = t2doc at . unType

encloseBranches :: [Doc AnsiStyle] -> Doc AnsiStyle
encloseBranches [] = lbrace <> rbrace
encloseBranches bs =
  sep [lbrace
      , nest 4 (vsep (map (<> semi)  bs))
      , rbrace]

branch2doc :: SElimBranch -> Doc AnsiStyle
branch2doc b =
  sep [ pretty (elimCon b) <+>
        sep (map pretty (elimConArgs b)) <+>
        opColor (pretty ":="), t2doc False (elimRes b)]

-- | Pretty printing de términos (Doc)
t2doc :: Bool     -- Debe ser un átomo? 
      -> STerm    -- término a mostrar
      -> Doc AnsiStyle
t2doc at (Lit i) = constColor (pretty (show i))
t2doc at SSuc = opColor (pretty "suc")
t2doc at SNat = opColor (pretty "Nat")
t2doc at SRefl = opColor (pretty "refl")
t2doc at (SEq t u) =
  parenIf at $
  t2doc True t <+> opColor (pretty "=") <+> t2doc True u
t2doc at (SV x) = name2doc x
t2doc at (SLam arg t) =
  parenIf at $
  sep [ opColor (pretty "\\") <>
        arg2doc arg <>
        opColor dot
      , nest 4 (t2doc False t)]
t2doc at t@(SApp _ _) =
  let (f, as) = collectApp t in
    parenIf at $
    t2doc True f <+> sep (map (t2doc True) as)
t2doc at (SElim t bs) =
  parenIf at $
  keywordColor (pretty "elim") <+>
  t2doc False t <+>
  encloseBranches (map branch2doc bs)
t2doc at (SFix f arg ty t) =
  parenIf at $
  sep [sep [ keywordColor (keywordColor $ pretty "fix")
            , name2doc f
            , arg2doc arg
            , opColor colon
            , ty2doc False ty
            , opColor dot]
      , nest 4 (t2doc False t)]
t2doc at t@(SPi _ _) =
  let pis = collectPi t
  in  parenIf at $ sep pis
t2doc _ (SSort (Set 0)) = keywordColor (pretty "Set")
t2doc at (SSort (Set i)) = 
  parenIf at $
  keywordColor (pretty "Set") <>
  constColor (pretty (show i))
t2doc at (SAnn t ty) =
  parenIf at $
  t2doc False t <> opColor colon <> ty2doc False ty

decl2doc :: SDecl -> Doc AnsiStyle
decl2doc (SDecl n args ty t) =
  sep [sep [name2doc n
          <+> sep (map arg2doc args)
          , opColor colon
          , ty2doc False ty]
      , opColor (pretty ":=")
      , t2doc False t]

render :: Doc AnsiStyle -> String
render = unpack . renderStrict . layoutSmart defaultLayoutOptions

ppTerm :: STerm -> String
ppTerm = render . t2doc False

ppType :: SType -> String
ppType = render . ty2doc False

ppDecl :: SDecl -> String
ppDecl = render . decl2doc