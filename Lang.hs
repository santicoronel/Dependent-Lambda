module Lang where

--import SLang

type Name = String

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
  -- TODO este caso es medio raro
  -- no quiero pasarle mas info en la introduccion
  -- pero me gustaria bindear un argumento en la eliminacion
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
data Constructor = Constructor {
  conName :: Name,
  conType :: Type,
  conArity :: Int
} deriving Show

instance Eq Constructor where
  c == d = conName c == conName d

-- TODO chequear q no haya argumentos repetidos
-- TODO pasar a locally nameless
data ElimBranch = ElimBranch {
  elimCon :: ConHead,
  elimConArgs :: [Name],
  elimRes :: Term
} deriving (Eq, Show)

infixl 9 :@:

-- TODO hago lo de la lista de elims o no??
-- tiene sentido hacerlo tambien para los constructores la verdá
-- no se si me complejiza mucho el typeChecker
-- TODO tengo un problema con el unionfind y name shadowing
-- podria tener un mapa de variables a nodos del uf
data Term =
  -- TODO pensar si estoy aprovechando los xes
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