module MinHS.TyInfer where

import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))
import Data.Monoid (Monoid (..), (<>))
import qualified MinHS.Env as E
import MinHS.Subst
import MinHS.Syntax
import MinHS.TCMonad

primOpType :: Op -> QType
primOpType Gt = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg = Ty $ Base Int `Arrow` Base Int
primOpType Fst = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _ = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True" = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()" = Just $ Ty $ Base Unit
constType "Pair" =
  Just $
    Forall "a" $
      Forall "b" $
        Ty $
          TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl" =
  Just $
    Forall "a" $
      Forall "b" $
        Ty $
          TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr" =
  Just $
    Forall "a" $
      Forall "b" $
        Ty $
          TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _ = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
  where
    tv' (TypeVar x) = [x]
    tv' (Prod a b) = tv a `union` tv b
    tv' (Sum a b) = tv a `union` tv b
    tv' (Arrow a b) = tv a `union` tv b
    tv' (Base c) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do
  (p', tau, s) <- runTC $ inferProgram initialGamma program
  return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst

unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do
  x' <- fresh
  unquantify'
    (i + 1)
    ((show i =: x') <> s)
    (substQType (x =: TypeVar (show i)) t)

unify :: Type -> Type -> TC Subst
unify (TypeVar t1) (TypeVar t2)
  | t1 == t2 = return emptySubst
  | otherwise = return (t1 =: (TypeVar t2))
unify (Base t1) (Base t2)
  | t1 == t2 = return emptySubst
  | otherwise = typeError $ TypeMismatch (Base t1) (Base t2)
unify (Prod t11 t12) (Prod t21 t22) =
  do
    u1 <- unify t11 t21
    u2 <- unify t12 t22
    return (u1 <> u2)
unify (Sum t11 t12) (Sum t21 t22) =
  do
    u1 <- unify t11 t21
    u2 <- unify t12 t22
    return (u1 <> u2)
unify (Arrow t11 t12) (Arrow t21 t22) =
  do
    u1 <- unify t11 t21
    u2 <- unify t12 t22
    return (u1 <> u2)
unify (TypeVar v) t
  | elem v (tv t) = typeError $ OccursCheckFailed v t
  | otherwise = return (v =: t)
unify t (TypeVar v) = unify (TypeVar v) t
unify x y = typeError $ MalformedAlternatives

generalise :: Gamma -> Type -> QType
generalise g t =
  let diff = (tv t) \\ (tvGamma g)
   in foldl (\a -> \b -> Forall b a) (Ty t) diff

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env bs =
  error $ show $ bs
  
  -- error
  --   "implement me! don't forget to run the result substitution on the"
  --   "entire expression using allTypes from Syntax.hs"

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)

inferExp g (Num n) = return (Num n, Base Int, emptySubst)

inferExp g (Var i) =
  case E.lookup g i of
    Just v -> do
      v' <- unquantify v
      return (Var i, v', emptySubst)
    Nothing -> typeError $ NoSuchVariable i

inferExp g (Con i) =
  case constType i of
    Just qtype -> do
      type' <- unquantify qtype
      return (Con i, type', emptySubst)
    Nothing -> typeError $ NoSuchConstructor i

inferExp g (Prim op) =
  do
    type' <- unquantify (primOpType op)
    return (Prim op, type', emptySubst)

inferExp g (App e1 e2) =
  do
    (exp1, t1, subst1) <- inferExp g e1
    (exp2, t2, subst2) <- inferExp (substGamma subst1 g) e2
    alpha <- fresh
    unifier <- unify (substitute subst2 t1) (Arrow t2 alpha)
    return (App e1 e2, (substitute unifier alpha), unifier <> subst2 <> subst1) --- what if e1 and e2 are qualtifier types

inferExp g (If e e1 e2) =
  do
    (exp, t, subst) <- inferExp g e
    unifier <- unify t (Base Bool)
    (exp1, t1, subst1) <- inferExp (substGamma (unifier <> subst) g) e1
    (exp2, t2, subst2) <- inferExp (substGamma (subst1 <> unifier <> subst) g) e2
    unifier' <- unify (substitute subst2 t1) t2
    return (If e e1 e2, (substitute unifier' t2), unifier <> subst2 <> subst1 <> unifier <> subst)

-- Note: this is the only case you need to handle for case expressions
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do
  (exp, t, subst) <- inferExp g e
  alphal <- fresh
  (exp1, tl, subst1) <- inferExp (substGamma subst (E.add g ((x, Ty alphal)))) e1
  alphar <- fresh
  (exp2, tr, subst2) <- inferExp (substGamma (subst <> subst1) (E.add g ((y, Ty alphar)))) e2
  unifier <- unify (substitute (subst <> subst1 <> subst2) (alphal `Sum` alphar)) (substitute (subst1 <> subst2) t)
  unifier' <- unify (substitute (unifier <> subst2) tl) (substitute unifier tr)
  return ((Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]), (substitute (unifier <> unifier') tr), unifier' <> unifier <> subst2 <> subst1 <> subst)
inferExp g (Case e _) = typeError MalformedAlternatives

inferExp g (Recfun (Bind f maybeQtype [x] e)) = do
  alpha1 <- fresh
  alpha2 <- fresh
  let g' = E.addAll g [(x, Ty alpha1), (f, Ty alpha2)]
  (exp, t, subst) <- inferExp g' e
  unifier <- unify (substitute subst alpha2) (Arrow (substitute subst alpha1) t)
  return ((Recfun (Bind f maybeQtype [x] e)), substitute unifier (Arrow (substitute subst alpha1) t), unifier <> subst)
inferExp g _ = error "Implement me!"

-- inferExp g (Let bindings e) =




test :: TC (Exp, Type, Subst)
-- test = inferExp initialGamma (Num 5)
-- test =  inferExp (E.add  initialGamma ("a", Ty $ Base Unit ) )  (Var "a")
-- test =  inferExp (E.add  initialGamma ("a", primOpType Fst))  (Var "a")
-- test =  inferExp (E.add  initialGamma ("a", primOpType Fst))  (Con "()")
-- test =  inferExp (E.add  initialGamma ("a", primOpType Fst))  (Con "Pair")
-- test =  inferExp (E.add  initialGamma ("a", primOpType Fst))  (Con "Inl")
-- test =  inferExp (E.add  initialGamma ("a", primOpType Fst))  (Prim Add)
-- test =  inferExp (E.add  initialGamma ("a", primOpType Fst))  (App (Prim Add) (Num 5))
test = inferExp (E.add initialGamma ("a", primOpType Fst)) (App (Prim Add) (Num 5))

subTest :: TC (Exp, Type, Subst)
subTest = do
  sub <- unify (Arrow (Base Int) (Arrow (Base Int) (Base Int))) (Arrow (Base Int) (TypeVar "X"))
  return (Num 1, Base Int, sub)

generaliseTest :: QType
generaliseTest = generalise (E.add initialGamma ("a", primOpType Fst)) (Arrow (TypeVar "A") (TypeVar "B"))

diffTest' :: Gamma -> Type -> [Id]
diffTest' g t = (tv t) \\ (tvGamma g)

diffTest :: [Id]
diffTest = diffTest' (E.add initialGamma ("A", primOpType Fst)) (TypeVar "A")

subTest2 = do
  sub <- unify (Arrow (Base Int) (Base Int)) (TypeVar "X")
  return (Num 1, Base Int, sub)

runTest :: TC a -> Either TypeError a
runTest t = runTC t