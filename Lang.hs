module Lang where

--import SLang

type Name = String

data Var = Bound Name | Global Name deriving (Eq, Show)

newtype Scope a = Scope { unscope :: a } deriving (Eq, Show) -- Info?

type ScopedTerm = Scope Term

-- incluyo sort?
data Type = Type { unType :: Term } deriving (Eq, Show)

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
  | DataCon Name
  deriving (Eq, Show)

data DataType =
  Nat
  | Eq Term Term
  | DataT Name
  deriving (Eq, Show)

data DataDef = DataDef { 
  dataName :: Name,
  dataSort :: Sort,
  dataParams :: [Type],
  dataType :: Type,
  dataCons :: [Constructor]
} deriving (Eq, Show)

data Constructor = Constructor {
  conName :: Name,
  conType :: Type
} deriving (Eq, Show)

data ElimBranch = ElimBranch {
  elimCon :: ConHead,
  elimConArgs :: [Name],
  elimRes :: Term
} deriving (Eq, Show)

infixl 9 :@:
data Term =
  V Var
  | Lit Int
  | Lam Arg (Scope Term)
  | Term :@: Term
  -- para aplicacion parcial eta expandimos??
  -- yo diria q no
  | Con ConHead
  | Data DataType
  -- considerar ´elim_as_in_return_...´ https://coq.inria.fr/doc/v8.13/refman/language/core/inductive.html#the-match-with-end-construction
  | Elim Term [ElimBranch]
  | Fix Name Arg Type [ElimBranch]
  | Pi Arg (Scope Type)
  | Sort Sort
  | Bot
  | Ann Term Type
  deriving (Eq, Show)

natTy :: Type
natTy = Type (Data Nat)

eqTy :: Term -> Term -> Type
t `eqTy` u = Type (Data (Eq t u))

{-
i Show Lam where
  show = nstanceshow . name

(!!) :: [a] -> Int -> Maybe a
xs      !! i | i < 0  = error "!!: negative index"
[]      !! _          = Nothing
(x:xs)  !! 0          = Just x
(x:xs)  !! i          = xs !! (i - 1)

name :: Lam -> NamedLam
name = go fresh []
  where vs = ['x','y', 'z'] ++ ['a' .. 'w']
        fresh = map (\x -> [x]) vs ++ [x : show n | x <- vs, n <- [1..]]
        go f e (Bound i) = case e !! i of
                            Just x -> Var x
                            Nothing -> error $ 
                              "error en elaboracion: binder " ++ show i ++ " fuera de rango."
        go f e (Lam t)   =  let x : f' = f
                                t' = go f' (x : e) t
                            in case t' of
                                NLam xs u -> NLam (x:xs) u
                                _         -> NLam [x] t'
        go f e (t :@: u) = NApp (go f e t) (go f e u)

elabLam :: NamedLam -> Lam
elabLam = go []
  where go e (Var x) = case elemIndex x e of
                          Just i -> Bound i
                          Nothing -> error $ "variable " ++ x ++ " no existe" 
        go e (NLam [x] t) = Lam $ go (x : e) t
        go e (NLam (x:xs) t) = Lam $ go (x : e) (NLam xs t)
        go e (NLam xs t) = foldr (const Lam) (go (reverse xs ++ e) t) xs 
        go e (NApp t u) = go e t :@: go e u


reduceLam :: Lam -> Lam
reduceLam = etaReduce . reduceNormal

-- esta roto esto :|
-- prolly falta ajustar binders
reduceCBN :: Lam -> Lam
reduceCBN t = uncurry (close 0) (runState  (go t) [])
  where go :: Lam -> State [Lam] Lam
        go (Bound i) = do e <- get
                          case e !! i of
                            Just t -> go t
                            Nothing -> error "reduceCBN: binder fuera de rango"
        go (Lam t) = return (Lam t)
        go (t :@: u) =  do  r <- go t
                            modify (u :)
                            case r of
                              Lam t' -> go t'

        close d (Bound i) e
          | i < d = Bound i
          | otherwise = case e !! (i - d) of
                          Just t -> t
                          Nothing -> error "close: binder fuera de rango"
        close d (Lam t) e = close (d + 1) t e
        close d (t :@: u) e = close d t e :@: close d u e

reduceNormal :: Lam -> Lam
reduceNormal = reduceCDEK                        

type Depth = Int

data E = NB Depth | E Env Lam
type Env = [E]

data Frame = Abs Env | AppL Env Lam | AppR Lam
type Kont = [Frame]

data Val = UB Int | Clos Env Lam | VApp Lam

reduceCDEK :: Lam -> Lam
reduceCDEK t = seek t 0 [] []

seek :: Lam -> Depth -> Env -> Kont -> Lam
seek (Bound i) d e k = case e !! i of
                        Nothing -> error "seek: binder fuera de rango"
                        Just v -> case v of
                                    NB d' -> destroy (UB (d - d')) d k
                                    E e' t -> seek t d e' k
seek (Lam t) d e k@(AppL _ _ : _) = destroy (Clos e t) d k  -- redex
seek (Lam t) d e k = seek t (d + 1) (NB (d + 1) : e) (Abs e : k)
seek (t :@: u) d e k = seek t d e (AppL e u : k)

destroy :: Val -> Depth -> Kont -> Lam
-- no kont
destroy v _ [] = toLam v
-- abs
destroy v d (Abs e : k) = destroy (Clos e (toLam v)) (d - 1) k 
-- Aplicacion a izquierda
destroy (Clos e t) d (AppL e' u : k) = seek t d (E e' u : e) k
destroy v d (AppL e u : k) = seek u d e (AppR (toLam v) : k)
-- Aplicacion a derecha
destroy v d (AppR t : k) = destroy (VApp (t :@: toLam v)) d k

toLam :: Val -> Lam
toLam (UB i) = Bound i
toLam (Clos _ t) = Lam t
toLam (VApp t) = t

-- funciona pero malaso
-- locally nameless taria bueno jijis
reduceNormalWithSubst :: Lam -> Lam
reduceNormalWithSubst (Bound i) = error "reduceNormal: binder fuera de rango"
reduceNormalWithSubst t = go t  
  where go (Bound i) = Bound i
        go (Lam t :@: u) = go (subst 0 t u)
        go (Bound i :@: u) = Bound i :@: go u
        go (t :@: u) = go (go t :@: u)
        go (Lam t) = Lam (go t)
        subst d (Bound i) u
          | d == i = u
          | otherwise = Bound i
        subst d (Lam t) u = Lam $ subst (d + 1) t (shift 0 u)
        subst d (t :@: t') u = subst d t u :@: subst d t' u
        shift d (Bound i)
          | i < d = Bound i
          | otherwise = Bound (i + 1)
        shift d (t :@: u) = shift d t :@: shift d u
        shift d (Lam t) = Lam $ shift (d + 1) t
        

update :: [a] -> Int -> a -> Maybe [a]
update _ i _ | i < 0 = error "update: negative index"
update [] _ _ = Nothing
update (_:xs) 0 x = Just (x:xs)
update (x:xs) i y = (x:) <$> update xs (i - 1) y

-- TODO hacerlo mas eficiente CEK style
etaReduce :: Lam -> Lam
etaReduce t = evalState (go t) []
  where go :: Lam -> State [Bool] Lam
        go (Bound i) = do e <- get
                          case update e i True of
                            Nothing -> error "etaReduce: binder fuera de rango"
                            Just e' -> put e' >> return (Bound i)
        go t@(Lam (u :@: Bound 0)) =
          do  modify (False :)
              u' <- go u
              e' <- get
              let f : e = e'
              put e
              if f then return t else return (unshift u')
        go (Lam t) = do modify (False :)
                        t' <- go t
                        modify tail
                        return (Lam t')
        go (t :@: u) = (:@:) <$> go t <*> go u

-- esto es malardo
unshift :: Lam -> Lam
unshift = go 0
  where go d (Bound i) = if i == d + 1 then Bound d else Bound i
        go d (Lam t) = Lam (go (d + 1) t)
        go d (t :@: u) = go d t :@: go d u
  -}