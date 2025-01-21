module Lang where
import Common

type Name = String

data Definition decl daty = PDecl decl | PData daty 

type SProgram = [Definition SDecl SDataDecl]
type Program = [Definition Decl DataDef]

data Decl = Decl {
  declName :: Name,
  declDef :: Term
} deriving Show

-- TODO let rec
data SDecl = SDecl {
  sdeclName :: Name,
  sdeclArgs :: [SArg],
  sdeclType :: SType,
  sdeclDef :: STerm
} deriving Show


data DataDecl' ty cons = DataDecl {
  dataDeclName :: Name,
  dataDeclType :: ty,
  dataDeclCons :: [cons]
}
type SDataDecl = DataDecl' SType SConsDecl 
type DataDecl = DataDecl' Type ConsDecl

data ConsDecl' ty = ConsDecl {
  consDeclName :: Name,
  consDeclType :: ty
}

type SConsDecl = ConsDecl' SType
type ConsDecl = ConsDecl' Type


-- TODO type alias
data Var =
  Bound Int
  | Free Int
  | Global Name deriving (Eq, Show)


-- incluyo sort?
newtype Type' t = Type { unType :: t } deriving Eq

instance Show t => Show (Type' t) where
  show (Type t) = show t

type Type = Type' Term
type SType = Type' STerm

newtype Sort' = Set Int deriving (Eq, Show)

type Sort = Sort'
type SSort = Sort'

set :: Int -> Type
set i = Type $ Sort $ Set i

data Arg' n ty = Arg {
  argName :: n,
  argType :: ty
} deriving Eq

instance (Show n, Show ty) => Show (Arg' n ty) where
  show (Arg n ty) = "(" ++ show n ++ " : " ++ show ty ++")"

type Arg = Arg' Name Type
type SArg = Arg' [Name] SType

data ConHead = 
  Zero
  | Suc
  | Refl
  | DataCon Constructor
  deriving (Eq, Show)

-- TODO hacer como constructor?
data DataType =
  Nat
  | Eq Term Term
  | DataT Name
  deriving Eq

instance Show DataType where
  show Nat = "Nat"
  show (Eq t u) = "(" ++ show t ++ " = " ++ show u ++ ")"
  show (DataT dn) = dn

-- MAYBE meter Eq t u aca dentro
data DataDef = DataDef { 
  dataName :: Name,
  dataParams :: [Type],
  dataType :: Type,
  dataSort :: Sort,
  dataArity :: Int,
  dataCons :: [Constructor]
} deriving Show

instance Eq DataDef where
  d == e = dataName d == dataName e

data Constructor = Constructor {
  conName :: Name,
  conType :: Type,
  conArity :: Int
} deriving Show

instance Eq Constructor where
  c == d = conName c == conName d

data ElimBranch' c t = ElimBranch {
  elimCon :: c,
  elimConArgs :: [Name],
  elimRes :: t
} deriving (Eq, Show)

type ElimBranch = ElimBranch' ConHead Term
type SElimBranch = ElimBranch' Name STerm


-- TODO multiargs
data STerm =
  Lit Int
  | SSuc
  | SNat
  | SRefl
  | SEq STerm STerm
  | SV Name
  | SLam SArg STerm
  | SApp STerm STerm
  | SElim STerm [SElimBranch]
  | SFix Name SArg SType STerm
  | SPi SArg SType
  | SSort SSort
  | SAnn STerm SType
  deriving (Eq, Show)

infixl 9 :@:

-- NICETOHAVE marcar si una var es recursiva
-- asi puedo no expandir globales tmb
-- tendria que tener un open/close especial
-- pero no tendria q consultar siempre el entorno

-- TODO let
data Term =
  V Var
  | Lam Arg Term
  | Term :@: Term
  | Con ConHead
  | Data DataType
  -- considerar ´elim_as_in_return_...´ https://coq.inria.fr/doc/v8.13/refman/language/core/inductive.html#the-match-with-end-construction
  | Elim Term [ElimBranch]
  | Fix Name Arg Type Term -- TODO sacar type
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

refl :: Term
refl = Con Refl

bound :: Int -> Term
bound = V . Bound

eqTy :: Term -> Term -> Type
t `eqTy` u = Type (Data (Eq t u))

-- TODO mejores nombres

getArgs :: Term -> (Term, [Term])
getArgs = go []
  where
    go as (t :@: u) = go (u : as) t
    go as f = (f, as)

consArgTypes :: ConHead -> [Type]
consArgTypes Zero = []
consArgTypes Suc = [natTy]
consArgTypes Refl = []
consArgTypes (DataCon c) = map argType $ snd $ dataConsArgTypes c

dataConsArgTypes :: Constructor -> (Type, [Arg])
dataConsArgTypes = getArgsTypes . unType . conType

getArgsTypes :: Term -> (Type, [Arg])
getArgsTypes (Pi arg ty) =
  let (rty, as) = getArgsTypes (unType ty) 
  in (rty, arg : as)
getArgsTypes ty = (Type ty, [])

inspectData :: Term -> Maybe (DataType, [Term])
inspectData = go []
  where
    go as (Data dt) = Just (dt, as)
    go as (t :@: u) = go (u : as) t
    go _ _ = Nothing

findBranch :: ConHead -> [ElimBranch] -> Maybe (ElimBranch, [ElimBranch])
findBranch = findWith elimCon id

findAllBranches :: [ConHead] -> [ElimBranch] -> Either ElimBranch [(ConHead, Maybe ElimBranch)]
findAllBranches [] [] = Right []
findAllBranches [] (b : _) = Left b
findAllBranches (c : cs) [] = ((c, Nothing) :) <$> findAllBranches cs []  
findAllBranches (c : cs) bs = case findBranch c bs of
    Nothing -> ((c, Nothing) :) <$> findAllBranches cs bs
    Just (b, bs') -> ((c, Just b) :) <$> findAllBranches cs bs'


freeIn :: Int -> Term -> Bool
freeIn x t = Free x `occursIn` t

occursIn :: Var -> Term -> Bool
occursIn v (V u) = v == u
occursIn v (Lam arg t) =
  occursInType v (argType arg) || occursIn (shiftVar 1 v) t
occursIn v (t :@: u) = occursIn v t || occursIn v u
occursIn v (Elim t bs) = or (occursIn v t : map (occursInBranch v) bs)
occursIn v (Fix _ arg ty t) =
  occursInType v (argType arg)
  || occursInType (shiftVar 1 v) ty
  || occursIn (shiftVar 2 v) t
occursIn v (Pi arg ty) =
  occursInType v (argType arg)
  || occursInType (shiftVar 1 v) ty
occursIn v (Ann t ty) =
  occursIn v t
  || occursInType v ty  
occursIn _ _ = False

occursInType :: Var -> Type -> Bool
occursInType v = occursIn v . unType

occursInBranch :: Var -> ElimBranch -> Bool
occursInBranch v b = occursIn (shiftVar (length $ elimConArgs b) v) (elimRes b)

shiftVar :: Int -> Var -> Var
shiftVar i (Bound j) = Bound (j + 1)
shiftVar _ v = v