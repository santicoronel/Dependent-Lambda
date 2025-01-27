module Error where

import Lang

-- TODO hacer bien
-- MAYBE parametrizar para resugarear antes de printear
data TypeError =
  EFun Type
  | EIncomplete Term
  | EEq Term Term
  | ECheckEq Type
  | ENotType Term
  | ECasesMissing
  | EManyCases
  | ENotData Type
  | EUnifError Term Term
  -- TODO revisar este
  | EIncompleteBot
  | ENeq Term Term
  | ENeqBranch
  | EGlobalEx Name
  | ECheckFun Term Type
  | EWrongCons ConHead
  | EDataSort Constructor Type Sort
  | EPositivity Type DataDef DataDef
  deriving Show