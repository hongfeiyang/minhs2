module MinHS.TyInfer where

import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))
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
inferProgram g [Bind name _ [] e] = do
  (exp, t, subst) <- inferExp g e
  return ([Bind "main" (Just $ generalise g t) [] exp], t, subst)

-- case generalise g (substitute s t) of
--   Ty t -> return ([Bind "main" (Just $ Ty (substitute s t)) [] exp], substitute s t, s)
--   t' -> return ([Bind "main" (Just t') [] exp], substitute s t, s)
inferProgram env bs = error "implement me! don't forget to run the result substitution on the entire expression using allTypes from Syntax.hs"

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
    -- traceM ("e1 in App is: " ++ show e1)
    -- traceM ("e2 in App is: " ++ show e2)
    -- traceM ("exp1 in App is: " ++ show exp1)
    -- traceM ("exp2 in App is: " ++ show exp2)
    -- traceM ("type in App is : " ++ show (substitute unifier alpha))
    -- traceM ("subst in App is : " ++ show (unifier <> subst2 <> subst1))
    return (allTypes (substQType (unifier <> subst2 <> subst1)) (App exp1 exp2), substitute unifier alpha, unifier <> subst2 <> subst1) --- what if e1 and e2 are qualtifier types
inferExp g (If e e1 e2) =
  do
    (exp, t, subst) <- inferExp g e
    unifier <- unify t (Base Bool)
    (exp1, t1, subst1) <- inferExp (substGamma (unifier <> subst) g) e1
    (exp2, t2, subst2) <- inferExp (substGamma (subst1 <> unifier <> subst) g) e2
    unifier' <- unify (substitute subst2 t1) t2

    -- traceM ("e in If is: " ++ show e)
    -- traceM ("e1 in If is: " ++ show e1)
    -- traceM ("e2 in If is: " ++ show e2)
    -- traceM ("exp in If is: " ++ show exp)
    -- traceM ("exp1 in If is: " ++ show exp1)
    -- traceM ("exp2 in If is: " ++ show exp2)

    return (If exp exp1 exp2, substitute unifier' t2, unifier <> subst2 <> subst1 <> unifier <> subst)

-- Note: this is the only case you need to handle for case expressions
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do
  (exp, t, subst) <- inferExp g e
  alphal <- fresh
  (exp1, tl, subst1) <- inferExp (substGamma subst (E.add g (x, Ty alphal))) e1
  alphar <- fresh
  (exp2, tr, subst2) <- inferExp (substGamma (subst <> subst1) (E.add g (y, Ty alphar))) e2
  unifier <- unify (substitute (subst <> subst1 <> subst2) (alphal `Sum` alphar)) (substitute (subst1 <> subst2) t)
  unifier' <- unify (substitute (unifier <> subst2) tl) (substitute unifier tr)

  -- traceM ("e1 in Case is: " ++ show e1)
  -- traceM ("e2 in Case is: " ++ show e2)
  -- traceM ("exp1 in Case is: " ++ show exp1)
  -- traceM ("exp2 in Case is: " ++ show exp2)

  return (Case e [Alt "Inl" [x] exp1, Alt "Inr" [y] exp2], substitute (unifier <> unifier') tr, unifier' <> unifier <> subst2 <> subst1 <> subst)
inferExp g (Case e _) = typeError MalformedAlternatives
--
-- Recfun
inferExp g (Recfun (Bind f maybeQtype [x] e)) = do
  alpha1 <- fresh
  alpha2 <- fresh
  let g' = E.addAll g [(x, Ty alpha1), (f, Ty alpha2)]
  (exp, t, subst) <- inferExp g' e
  unifier <- unify (substitute subst alpha2) (Arrow (substitute subst alpha1) t)

  let returnType = substitute unifier (Arrow (substitute subst alpha1) t)
  let returnSubst = unifier <> subst
  let returnExp = allTypes (substQType returnSubst) $ Recfun (Bind f (Just (Ty returnType)) [x] exp)

  -- traceM ("maybeQtype in Recfun is: " ++ show maybeQtype)
  -- traceM ("returnType in Recfun is: " ++ show returnType)
  -- traceM ("returnSubst in Recfun is: " ++ show returnSubst)
  -- traceM ("returnExp in Recfun is: " ++ show returnExp)

  return (returnExp, returnType, returnSubst)

-- Let
inferExp g (Let [Bind v maybeVType [] body] e) = do
  (exp, t, subst) <- inferExp g body
  let _g = substGamma subst g
  let _t = generalise _g t
  let g' = E.add _g (v, _t)
  (exp', t', subst') <- inferExp g' e

  let returnSubst = subst' <> subst
  let returnExp = allTypes (substQType returnSubst) $ Let [Bind v (Just (Ty t)) [] exp] exp'

  -- traceM ("maybeQtype in Recfun is: " ++ show maybeQtype)
  traceM ("returnType in Let is: " ++ show t')
  traceM ("returnSubst in Let is: " ++ show returnSubst)
  traceM ("generalisation in Let is: " ++ show _t)
  -- traceM ("returnExp in Let is: " ++ show returnExp)

  return (returnExp, t', returnSubst) -- test this
inferExp g x = error ("Unknown expression: " ++ show x)

test :: TC (Exp, Type, Subst)
-- test = inferExp initialGamma (Num 5)
-- test =  inferExp (E.add  initialGamma ("a", Ty $ Base Unit ) )  (Var "a")
-- test =  inferExp (E.add  initialGamma ("a", primOpType Fst))  (Var "a")
-- test =  inferExp (E.add  initialGamma ("a", primOpType Fst))  (Con "()")
-- test =  inferExp (E.add  initialGamma ("a", primOpType Fst))  (Con "Pair")
-- test =  inferExp (E.add  initialGamma ("a", primOpType Fst))  (Con "Inl")
-- test =  inferExp (E.add  initialGamma ("a", primOpType Fst))  (Prim Add)
-- test =  inferExp (E.add  initialGamma ("a", primOpType Fst))  (App (Prim Add) (Num 5))
-- test =
--   inferExp
--     (E.addAll initialGamma [("x", Ty $ Base Int), ("y", Ty $ Base Int)])
--     (App (App (Prim Add) (Var "x")) (Var "y"))
test =
  inferExp
    initialGamma
    ( Let
        [Bind "x" (Just $ Ty $ Base Int) [] (Num 1)]
        ( Let
            [Bind "y" (Just $ Ty $ Base Int) [] (Num 2)]
            (App (App (Prim Add) (Var "x")) (Var "y"))
        )
    )

inferProgramTest =
  inferProgram
    initialGamma
    [ Bind
        "main"
        Nothing
        []
        ( Let
            [Bind "x" Nothing [] (Num 1)]
            ( Let
                [Bind "y" Nothing [] (Num 2)]
                ( Let
                    [Bind "f" Nothing [] (Recfun (Bind "f" Nothing ["z"] (Var "z")))]
                    ( If
                        (App (Var "f") (Con "True"))
                        (App (Con "Inl") (App (App (Prim Add) (Var "x")) (Var "y")))
                        (App (Con "Inr") (Var "x"))
                    )
                )
            )
        )
    ]

unexpectResult =
  Right
    ( [ Bind
          "main"
          (Just (Ty (Sum (Base Int) (Base Int))))
          []
          ( Let
              [ Bind
                  "x"
                  (Just (Ty (Base Int)))
                  []
                  (Num 1)
              ]
              ( Let
                  [Bind "y" (Just (Ty (Base Int))) [] (Num 2)]
                  ( Let
                      [ Bind
                          "f"
                          (Just (Ty (Arrow (TypeVar "a") (TypeVar "a"))))
                          []
                          (Recfun (Bind "f" (Just (Ty (Arrow (TypeVar "a") (TypeVar "a")))) ["z"] (Var "z")))
                      ]
                      (If (App (Var "f") (Con "True")) (App (Con "Inl") (App (App (Prim Add) (Var "x")) (Var "y"))) (App (Con "Inr") (Var "x")))
                  )
              )
          )
      ],
      Sum (Base Int) (Base Int),
      [ ("k", Base Int),
        ("l", Sum (TypeVar "j") (Base Int)),
        ("e", Base Int),
        ("i", Sum (Base Int) (TypeVar "f")),
        ("h", Base Int),
        ("g", Arrow (Base Int) (Base Int)),
        ("c", Base Bool),
        ("d", Base Bool),
        ("b", Arrow (TypeVar "a") (TypeVar "a"))
      ]
    )

expectedResult =
  Right
    ( [ Bind
          "main"
          (Just (Ty (Sum (Base Int) (Base Int))))
          []
          ( Let
              [Bind "x" (Just (Ty (Base Int))) [] (Num 1)]
              ( Let
                  [Bind "y" (Just (Ty (Base Int))) [] (Num 2)]
                  ( Let
                      [ Bind
                          "f"
                          (Just (Forall "a" (Ty (Arrow (TypeVar "a") (TypeVar "a")))))
                          []
                          (Recfun (Bind "f" (Just (Ty (Arrow (TypeVar "a") (TypeVar "a")))) ["z"] (Var "z")))
                      ]
                      ( If
                          (App (Var "f") (Con "True"))
                          (App (Con "Inl") (App (App (Prim Add) (Var "x")) (Var "y")))
                          (App (Con "Inr") (Var "x"))
                      )
                  )
              )
          )
      ],
      Sum (Base Int) (Base Int),
      [ ("b", Arrow (TypeVar "a") (TypeVar "a")),
        ("j", Base Int),
        ("f", Base Int),
        ("k", Base Int),
        ("l", Sum (Base Int) (Base Int)),
        ("e", Base Int),
        ("i", Sum (Base Int) (Base Int)),
        ("h", Base Int),
        ("g", Arrow (Base Int) (Base Int)),
        ("c", Base Bool),
        ("d", Base Bool)
      ]
    )

subTest :: TC (Exp, Type, Subst)
subTest = do
  sub <- unify (Arrow (Base Int) (Arrow (Base Int) (Base Int))) (Arrow (Base Int) (TypeVar "X"))
  return (Num 1, Base Int, sub)

generaliseTest :: QType
generaliseTest = generalise (E.add initialGamma ("a", primOpType Fst)) (Arrow (TypeVar "A") (TypeVar "B"))

diffTest' :: Gamma -> Type -> [Id]
diffTest' g t = tv t \\ tvGamma g

diffTest :: [Id]
diffTest = diffTest' (E.add initialGamma ("A", primOpType Fst)) (TypeVar "A")

subTest2 = do
  sub <- unify (Arrow (Base Int) (Base Int)) (TypeVar "X")
  return (Num 1, Base Int, sub)

runTest :: TC a -> Either TypeError a
runTest = runTC

inferProgramTest1 =
  inferProgram
    initialGamma
    [ Bind
        "main"
        Nothing
        []
        (Let [Bind "x" Nothing [] (Con "True"), Bind "y" Nothing [] (Num 1), Bind "z" Nothing [] (Con "()")] (Var "x"))
    ]

a =
  Right
    ( [ Bind
          "main"
          (Just (Forall "a" (Ty (Arrow (TypeVar "a") (TypeVar "a")))))
          []
          (Recfun (Bind "f" (Just (Ty (Arrow (TypeVar "a") (TypeVar "a")))) ["z"] (Var "z")))
      ],
      Arrow (TypeVar "a") (TypeVar "a"),
      [("b", Arrow (TypeVar "a") (TypeVar "a"))]
    )

b =
  Right
    ( [ Bind
          "main"
          (Just (Forall "a" (Ty (Arrow (TypeVar "a") (TypeVar "a")))))
          []
          (Recfun (Bind "f" (Just (Ty (Arrow (TypeVar "a") (TypeVar "a")))) ["z"] (Var "z")))
      ],
      Arrow (TypeVar "a") (TypeVar "a"),
      [("b", Arrow (TypeVar "a") (TypeVar "a"))]
    )