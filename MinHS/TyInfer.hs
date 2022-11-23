module MinHS.TyInfer where

import Data.Foldable (foldMap)
import Data.List (elemIndex, find, nub, sortBy, union, (\\))
import Data.Monoid (Monoid (..), (<>))
import Debug.Trace
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
  | otherwise = return (t2 =: TypeVar t1)
unify (Base t1) (Base t2)
  | t1 == t2 = return emptySubst
  | otherwise = typeError $ TypeMismatch (Base t1) (Base t2)
unify (Prod t11 t12) (Prod t21 t22) =
  do
    u1 <- unify t11 t21
    u2 <- unify (substitute u1 t12) (substitute u1 t22)
    return (u1 <> u2)
unify (Sum t11 t12) (Sum t21 t22) =
  do
    u1 <- unify t11 t21
    u2 <- unify (substitute u1 t12) (substitute u1 t22)
    return (u1 <> u2)
unify (Arrow t11 t12) (Arrow t21 t22) =
  do
    u1 <- unify t11 t21
    u2 <- unify (substitute u1 t12) (substitute u1 t22)
    return (u1 <> u2)
unify (TypeVar v) t
  | v `elem` tv t = typeError $ OccursCheckFailed v t
  | otherwise = return (v =: t)
unify t (TypeVar v) = unify (TypeVar v) t
unify x y = typeError MalformedAlternatives

generalise :: Gamma -> Type -> QType
generalise g t = let diff = tv t \\ tvGamma g in foldl (flip Forall) (Ty t) diff

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram g [Bind name maybeGivenQType [] e] = do
  (exp, t, subst) <- inferExp g e
  case maybeGivenQType of
    -- handle user supplied type
    -- for now this program is not able to handle situations where user supplied a forall type but we
    -- figure out the type should be more restricting, but it is able to handle the other way around
    Just givenQType -> do
      givenType <- unquantify givenQType
      case runTC (unify t givenType) of
        Right unifier -> do
          let returnSubst = subst <> unifier
          let allTypedExp = allTypes (substQType returnSubst) exp
          let returnType = substitute returnSubst t
          return ([Bind "main" (Just $ generalise g returnType) [] allTypedExp], returnType, returnSubst)
        Left err -> error $ show err
    Nothing -> do
      let allTypedExp = allTypes (substQType subst) exp
      return ([Bind "main" (Just $ generalise g t) [] allTypedExp], t, subst)
inferProgram env bs = error "implement me! don't forget to run the result substitution on the entire expression using allTypes from Syntax.hs"

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
    return (App exp1 exp2, substitute unifier alpha, unifier <> subst2 <> subst1)

--
-- If
inferExp g (If e e1 e2) =
  do
    (exp, t, subst) <- inferExp g e
    unifier <- unify t (Base Bool)
    case substitute (unifier <> subst) t of
      Base Bool -> do
        (exp1, t1, subst1) <- inferExp (substGamma (unifier <> subst) g) e1
        (exp2, t2, subst2) <- inferExp (substGamma (subst1 <> unifier <> subst) g) e2
        unifier' <- unify (substitute subst2 t1) t2
        return (If exp exp1 exp2, substitute unifier' t2, unifier' <> unifier <> subst2 <> subst1 <> subst)
      _ -> typeError $ TypeMismatch (Base Bool) t

-- Note: this is the only case you need to handle for case expressions
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do
  (exp, t, subst) <- inferExp g e
  alphal <- fresh
  (exp1, tl, subst1) <- inferExp (substGamma subst (E.add g (x, Ty alphal))) e1
  alphar <- fresh
  (exp2, tr, subst2) <- inferExp (substGamma (subst <> subst1) (E.add g (y, Ty alphar))) e2
  unifier <- unify (substitute (subst <> subst1 <> subst2) (alphal `Sum` alphar)) (substitute (subst1 <> subst2) t)
  unifier' <- unify (substitute (unifier <> subst2) tl) (substitute unifier tr)
  return (Case exp [Alt "Inl" [x] exp1, Alt "Inr" [y] exp2], substitute (unifier <> unifier') tr, unifier' <> unifier <> subst2 <> subst1 <> subst)
inferExp g (Case e _) = typeError MalformedAlternatives
--
-- Recfun
inferExp g (Recfun (Bind f maybeGivenQType args e)) = do
  -- alpha1 <- fresh (as in if recfun only have one argument)
  argsBindings <- bindArgsToFreshTypeVar args [] -- for multiple arguments
  alpha2 <- fresh

  let argsQTypeBindings = map (\a -> (fst a, Ty $ snd a)) argsBindings
  let g' = E.addAll g (argsQTypeBindings ++ [(f, Ty alpha2)])
  (exp, t, subst) <- inferExp g' e

  case maybeGivenQType of
    Just givenQType -> do
      -- user supplied a type, we need to see if this type is <= than our current type that we figured out,
      -- if it is then we use user supplied type, e.g. we figured out the type should be `forall a. a` but user wants to
      -- limit this to `Bool`, we must comply with user's preference and procceed with `a` replaced by `Bool`
      givenType <- unquantify givenQType
      (returnExp, returnType, returnSubst) <- getFuncReturnType givenType subst t argsBindings exp
      return (returnExp, returnType, returnSubst)
    Nothing -> do
      -- otherwise we figure out a type ourselves
      (returnExp, returnType, returnSubst) <- getFuncReturnType alpha2 subst t argsBindings exp
      return (returnExp, returnType, returnSubst)
  where
    getFuncReturnType givenType subst t argsBindings exp = do
      let functionType = foldr (\a b -> Arrow (substitute subst a) b) t (map snd argsBindings)
      unifier <- unify (substitute subst givenType) functionType
      let returnType = substitute unifier functionType
      let returnSubst = unifier <> subst
      let returnExp = Recfun (Bind f (Just (Ty returnType)) args exp)
      return (returnExp, returnType, returnSubst)

-- Let
inferExp g (Let bindings e) = do
  (g', sub, evaluatedBindings) <- evaluateAndAddAllBindingsToGammaOfLet g emptySubst bindings []
  (exp', t', subst') <- inferExp g' e
  return (Let evaluatedBindings exp', t', subst' <> sub)

--
-- Letrec
inferExp g (Letrec bindings e) = do
  (g', sub, evaluatedBindings) <- evaluateAndAddAllBindingsToGammaOfLetrec g emptySubst bindings []
  let orderedEvaluatedBindings = restoreBindOrder evaluatedBindings bindings
  (exp', t', subst') <- inferExp g' e
  return (Letrec orderedEvaluatedBindings exp', t', subst' <> sub)

--
-- support for multiple arguments in Bind
-- basically generate fresh typevars for all arguments of a function
bindArgsToFreshTypeVar :: [Id] -> [(Id, Type)] -> TC [(Id, Type)]
bindArgsToFreshTypeVar [] bindings = return $ reverse bindings
bindArgsToFreshTypeVar (id : ids) bindings = do
  alpha <- fresh
  bindArgsToFreshTypeVar ids ((id, alpha) : bindings)

--
-- multiple bindings add to Gamma,
evaluateAndAddAllBindingsToGammaOfLet :: Gamma -> Subst -> [Bind] -> [Bind] -> TC (Gamma, Subst, [Bind])
evaluateAndAddAllBindingsToGammaOfLet g sub [] r = return (g, sub, reverse r)
evaluateAndAddAllBindingsToGammaOfLet g sub ((Bind v maybeGivenQType args body) : xs) r = do
  (exp, t, subst) <- inferExp g body
  let _g = substGamma subst g
  let _t = generalise _g t
  let g' = E.add _g (v, _t)
  evaluateAndAddAllBindingsToGammaOfLet g' (subst <> sub) xs (Bind v (Just $ generalise g' t) args exp : r)

evaluateAndAddAllBindingsToGammaOfLetrec g sub [] r = return (g, sub, reverse r)
evaluateAndAddAllBindingsToGammaOfLetrec g sub ((Bind v maybeVType args body) : xs) r = do
  case runTC $ inferExp g body of
    -- only difference here is that if we have a unknown var that cannot be resolved of its type, we move it to the end
    -- and (hopefully) resolve other vars first to know this var's type
    Left (NoSuchVariable _) -> evaluateAndAddAllBindingsToGammaOfLetrec g sub (xs ++ [Bind v maybeVType args body]) r
    _ -> do
      (exp, t, subst) <- inferExp g body
      let _g = substGamma subst g
          _t = generalise _g t
          g' = E.add _g (v, _t)
       in evaluateAndAddAllBindingsToGammaOfLetrec g' (subst <> sub) xs (Bind v (Just $ generalise g' t) args exp : r)

-- restore the ordering of our re-ordered bindings (first argument)
-- to the original ordering (second argument) in letrec
restoreBindOrder :: [Bind] -> [Bind] -> [Bind]
restoreBindOrder xs ys =
  sortBy (\a b -> compareBindByIndexInList a b ys) xs

compareBindByIndexInList :: Bind -> Bind -> [Bind] -> Ordering
compareBindByIndexInList a b ys = case compareBindByIndexInList' a b ys of
  Just o -> o
  Nothing -> error "List sizes and binding names are different"

compareBindByIndexInList' :: Bind -> Bind -> [Bind] -> Maybe Ordering
compareBindByIndexInList' (Bind a _ _ _) (Bind b _ _ _) ys = do
  aInys <- find (\(Bind n' _ _ _) -> n' == a) ys
  aIndex <- elemIndex aInys ys
  bInys <- find (\(Bind n' _ _ _) -> n' == b) ys
  bIndex <- elemIndex bInys ys
  if aIndex >= bIndex
    then
      if aIndex > bIndex
        then return GT
        else return EQ
    else return LT
