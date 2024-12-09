module Lang where

--import SLang

type Name = String

-- TODO type allias
data Var =
  Bound Int
  | Free Int
  | Global Name deriving (Eq, Show)


-- incluyo sort?
newtype Type = Type { unType :: Term } deriving (Eq, Show)

newtype Sort = Set Int deriving (Eq, Show)

set :: Int -> Type
set i = Type $ Sort $ Set i

data Arg = Arg {
  argType :: Type,
  argName :: Name }
  deriving (Eq, Show)

data ConHead = 
  Zero
  | Suc
  | Refl
  | DataCon Constructor
  deriving (Eq, Show)

-- TODO hacer comoo constructor?
data DataType =
  Nat
  | Eq Term Term
  | DataT Name
  deriving (Eq, Show)

-- TODO tipo debe estar reducido
-- mejor: chequeo sintactico, no permitir cosa rara
data DataDef = DataDef { 
  dataName :: Name,
  dataSort :: Sort,
  dataParams :: [Type],
  dataType :: Type,
  dataArity :: Int,
  dataCons :: [Constructor]
} deriving Show

instance Eq DataDef where
  d == e = dataName d == dataName e

-- TODO tipo debe estar reducido
-- mejor: chequeo sintactico, simil data
data Constructor = Constructor {
  conName :: Name,
  conType :: Type,
  conArity :: Int
} deriving Show

instance Eq Constructor where
  c == d = conName c == conName d

-- TODO chequear q no haya argumentos repetidos
data ElimBranch = ElimBranch {
  elimCon :: ConHead,
  elimConArgs :: [Name],
  elimRes :: Term
} deriving (Eq, Show)

infixl 9 :@:

data Term =
  V Var
  | Lam Arg Term
  | Term :@: Term
  -- para aplicacion parcial eta expandimos??
  -- yo diria q no
  | Con ConHead
  | Data DataType
  -- considerar ´elim_as_in_return_...´ https://coq.inria.fr/doc/v8.13/refman/language/core/inductive.html#the-match-with-end-construction
  | Elim Term [ElimBranch]
  | Fix Name Arg Type Term
  | Pi Arg Type
  | Sort Sort
  | Ann Term Type
  deriving (Eq, Show)

var :: Int -> Term
var x = V (Free x)

natTy :: Type
natTy = Type (Data Nat)

zero :: Term
zero = Con Zero

suc :: Term -> Term
suc n = Con Suc :@: n 

eqTy :: Term -> Term -> Type
t `eqTy` u = Type (Data (Eq t u))

consArgTypes :: ConHead -> [Type]
consArgTypes Zero = []
consArgTypes Suc = [natTy]
consArgTypes Refl = []
consArgTypes (DataCon c) = getArgsTypes (unType $ conType c)

getArgsTypes :: Term -> [Type]
getArgsTypes (Pi arg ty) = argType arg : getArgsTypes (unType ty)
getArgsTypes ty = [Type ty]