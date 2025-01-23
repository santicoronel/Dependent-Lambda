module Error where

import Lang

-- TODO hacer bien

data TypeError =
  EGlobal Name
  | EFun Type
  | EIncomplete Term
  | EEq Term Term
  | ECheckEq Type
  | ENotType Term
  | ECasesMissing
  | EManyCases
  | EDataNoDef Name
  | ENotData Type
  | ENumberOfArgs ConHead
  | EUnifiable
  | ENotUnif
  | EUnifError Term Term
  | EIncompleteBot
  | ENeq Term Term
  | ENeqBranch
  | EGlobalEx Name
  | ECheckFun Term
  | EWrongCons ConHead
  | EDataSort Constructor Type Sort
  | EPositivity Type DataDef DataDef
  deriving Show