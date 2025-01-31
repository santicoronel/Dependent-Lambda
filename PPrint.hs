module PPrint where

import Lang
import Error
import Resugar

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
      align,
      cat,
      hsep,
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
collectPi (SPi args ty) = 
  (cat (map arg2doc args) <+> opColor (pretty "->")) : collectPi (unType ty)
collectPi (SFun aty rty) = 
  (ty2doc False aty <+> opColor (pretty "->")) : collectPi (unType rty)
collectPi ty = [t2doc False ty]

arg2doc :: SArg -> Doc AnsiStyle
arg2doc (Arg xs ty) =
  parens $
  hsep [sep $ map name2doc xs , opColor colon, ty2doc False ty]

encloseBranches :: [Doc AnsiStyle] -> Doc AnsiStyle
encloseBranches [] = lbrace <> rbrace
encloseBranches bs =
  sep [lbrace
      , nest 4 (vsep (punctuate semi bs))
      , rbrace]

branch2doc :: SElimBranch -> Doc AnsiStyle
branch2doc b =
  sep [ pretty (elimCon b) <+>
        sep (map pretty (elimConArgs b)) <+>
        opColor (pretty ":="), t2doc False (elimRes b)]

sort2doc :: Bool -> SSort -> Doc AnsiStyle
sort2doc _ (Set 0) = keywordColor (pretty "Set")
sort2doc at (Set i) = 
  parenIf at $
  keywordColor (pretty "Set") <>
  constColor (pretty (show i))

ty2doc :: Bool -> SType -> Doc AnsiStyle
ty2doc at = t2doc at . unType

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
  -- NICETOHAVE pensar parentesis
  t2doc False t <+> opColor (pretty "=") <+> t2doc False u
t2doc at (SV x) = name2doc x
t2doc at (SLam arg t) =
  parenIf at $
  sep [ opColor (pretty "\\") <>
        cat (map arg2doc arg) <>
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
t2doc at (SFix f args ty t) =
  parenIf at $
  sep [sep [ keywordColor (keywordColor $ pretty "fix")
            , name2doc f
            , cat (map arg2doc args)
            , opColor colon
            , ty2doc False ty
            , opColor dot]
      , nest 4 (t2doc False t)]
t2doc at t@(SPi _ _) =
  let pis = collectPi t
  in  parenIf at $ sep pis
t2doc at t@(SFun _ _) =
  let pis = collectPi t
  in  parenIf at $ sep pis 
t2doc at (SSort s) = sort2doc at s
t2doc at (SAnn t ty) =
  parenIf at $
  t2doc False t <> opColor colon <> ty2doc False ty

decl2doc :: SDecl -> Doc AnsiStyle
decl2doc (SDecl n args ty t _) =
  sep [sep [sep (name2doc n : map arg2doc args)
          , opColor colon
          , ty2doc False ty]
      , opColor (pretty ":=")
      , t2doc False t]

-- MAYBE ponerle estilo (color, ...) a los terminos
typeError2doc :: [Name] -> [Name] -> TypeError -> Doc AnsiStyle
typeError2doc _ _ (Other e) = pretty e
typeError2doc ns rs e = pretty "Error:" <+> align (go e)
  where
    go (EFun ty) =
      let sty = resugarType ns rs ty
      in  ty2doc False sty <+>
          pretty "no es un tipo función"
    -- TODO ver este caso
    go (EIncomplete t) =
      let st = resugar ns rs t
      in  pretty "no se pudo inferir el tipo de" <+>
          t2doc False st
    go (EEq t u) =
      let st = resugar ns rs t
          su = resugar ns rs u
      in  pretty "los términos" <+>
          align (vsep [
            t2doc False st
          , t2doc False su]) <+>
          pretty "no son comparables"
    go (ECheckEq ty) =
      let sty = resugarType ns rs ty
      in  ty2doc False sty <+>
          pretty "no es una igualdad"
    go (ENotType t) =
      let st = resugar ns rs t
      in  t2doc False st <+>
          pretty "no es un tipo"
    go ECasesMissing =
      pretty "casos faltantes en cláusula" <+>
      keywordColor (pretty "elim")
    go EManyCases =
      pretty "demasiados casos en cláusula" <+>
      keywordColor (pretty "elim")
    go (ENotData ty) =
      let sty = resugarType ns rs ty
      in  pretty "el tipo" <+>
          ty2doc False sty <+>
          pretty "no puede eliminarse por casos"
    go (EUnifError t u) =
      let st = resugar ns rs t
          su = resugar ns rs u
      in  pretty "no se pudo unificar los términos" <+>
          align (vsep [
            t2doc False st
          , t2doc False su])
    -- TODO revisar este caso
    go EIncompleteBot =
      pretty "no se pueden inferir casos faltantes."
    go (ENeq t u) =
      let st = resugar ns rs t
          su = resugar ns rs u
      in  pretty "no se pudo probar igualdad de los términos" <+>
          align (vsep [
            t2doc False st
          , t2doc False su])
    -- TODO ver este caso
    go ENeqBranch =
      pretty "no se puede probar igualdad de eliminaciones" <+>
      pretty "con distinto número de casos"
    go (EGlobalEx n) =
      pretty "variable" <+>
      name2doc n <+>
      pretty "ya está definida"
    go (ECheckFun t ty) =
      let st = resugar ns rs t
          sty = resugarType ns rs ty
      in  vsep [
          pretty "se esperaba un tipo función para" <+>
          t2doc False st
        , pretty "pero se encontró" <+>
          ty2doc False sty
          ]
    go (EWrongCons ch) =
      let cn = conHeadName ch
      in  pretty "constructor" <+>
          name2doc cn <+>
          pretty "inesperado en cláusula" <+>
          keywordColor (pretty "elim")
    go (EDataSort c ty s) =
      let cn = conName c
          sty = resugarType ns rs ty
      in  pretty "en la definición del constructor" <+>
          name2doc cn <+>
          pretty "el sort de" <+>
          ty2doc False sty <+>
          pretty "no es menor a" <+>
          sort2doc False s
    go (EPositivity ty dx di) =
      let sty = resugarType ns rs ty
          nx = dataName dx
          ni = dataName di
      in  pretty "el tipo" <+>
          ty2doc False sty <+>
          pretty "en la definicion de" <+>
          name2doc ni <+>
          pretty "no pasa el test de positividad para" <+>
          name2doc nx

terminationError2doc :: TerminationError -> Doc AnsiStyle
terminationError2doc e = pretty "Error:" <+> align (go e)
  where
    go (TError f) =
      pretty "no se pudo probar terminación para la función" <+>
      pretty f

render :: Doc AnsiStyle -> String
render = unpack . renderStrict . layoutSmart defaultLayoutOptions

ppTerm :: STerm -> String
ppTerm = render . t2doc False

ppType :: SType -> String
ppType = render . ty2doc False

ppDecl :: SDecl -> String
ppDecl = render . decl2doc

ppTypeError :: [Name] -> [Name] -> TypeError -> String
ppTypeError ns rs = render . typeError2doc ns rs

ppTerminationError :: TerminationError -> String
ppTerminationError = render . terminationError2doc
