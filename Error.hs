module Error where

import Lang

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
  | ENotUnif
  | EIncompleteBot
  | EUnifiable
  | ENeq Term Term