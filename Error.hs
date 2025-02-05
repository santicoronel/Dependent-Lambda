module Error where

import Lang

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
  | EIncompleteBot
  | ENeq Term Term
  | ENeqBranch
  | EGlobalEx Name
  | ECheckFun Term Type
  | EWrongCons ConHead
  | EDataSort Constructor Type Sort
  | EPositivity Type DataDef DataDef
  | Other String
  deriving Show

newtype TerminationError = TError Name deriving Show

data ElabError = ElabError String | DataError String
