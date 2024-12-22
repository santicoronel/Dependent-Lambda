module Error where

import Lang

-- TODO hacer bien

data TypeError =
  EFree Int
  | EGlobal Name
  | EFun Type
  | EIncomplete Term
  | EEq Term Term
  | EPartialEq
  | ECheck Type Type
  | ECheckEq Type
  | ENotType Term
  | ECasesMissing
  | EManyCases
  | EDataNoDef Name
  | ENotData Type
  | ENumberOfArgs ConHead
  | EUnifiable
  | ENotUnif
  | EUnifError
  | EIncompleteBot
  | ENeq Term Term
  | ENeqBranch
  | EGlobalEx Name
  | ECheckFun Term
  | EWrongCons ConHead
  deriving Show