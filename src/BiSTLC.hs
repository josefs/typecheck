{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module BiSTLC where

import Control.Lens hiding (Context)

-- An implementation of https://cybercat.institute/2025/01/28/bidirectional-typechecking/

data Type = TVar String | Unit | Function Type Type
  deriving (Eq, Show)

data TermSyn = Var String | App TermSyn TermChk | Down Type TermChk
  deriving (Show)

data TermChk = Lambda String TermChk | Up TermSyn
  deriving (Show)

type Context = [(String, Type)]

data Question = Synthesise Context TermSyn | Check Context Type TermChk
  deriving (Show)

data Answer = Synthesised Type | Checked | TypeError
  deriving (Show)

lam :: forall f. (Functor f) => (Question -> f Answer) -> Question -> f Answer
lam k (Check ctx (Function a b) (Lambda x t)) = k (Check ((x, a) : ctx) b t)
-- All the below is AI generated
{-
lam k (Synthesise ctx (App t1 t2)) = k (Synthesise ctx t1) <&> \case
  Synthesised (Function a b) -> k (Check ctx a t2)
  _ -> pure TypeError
lam k (Synthesise ctx (Down a t)) = k (Check ctx a t)
lam k (Synthesise ctx (Var x)) = case lookup x ctx of
  Just a -> pure (Synthesised a)
  Nothing -> pure TypeError
lam k (Check ctx a (Up t)) = k (Synthesise ctx t) <&> \case
  Synthesised b -> if a == b then pure Checked else pure TypeError
lam k _ = pure TypeError
-}
(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

app :: forall f. (MonadFail f) => (Question -> f Answer) -> Question -> f Answer
app k (Synthesise ctx (App t u)) = do
  Synthesised (Function a b) <- k (Synthesise ctx t)
  Checked <- k (Check ctx a u)
  return (Synthesised b)

type MonadicTraversal s t a b = forall f. (Monad f) => (a -> f b) -> s -> f t

rules :: MonadicTraversal Question Answer Question Answer
rules _ (Synthesise ctx (Var x)) = case lookup x ctx of
    Just a -> return (Synthesised a)
    Nothing -> return TypeError
rules k (Synthesise ctx (App t1 t2)) = k (Synthesise ctx t1) >>= \case
    Synthesised (Function a b) -> k (Check ctx a t2) >>= \case
        Checked -> return (Synthesised b)
        _ -> return TypeError
    _ -> return TypeError
rules k (Synthesise ctx (Down a t)) = k (Check ctx a t) >>= \case
    Checked -> return (Synthesised a)
    _ -> return TypeError
rules k (Check ctx (Function a b) (Lambda x t)) = k (Check ((x, a) : ctx) b t)
rules _ (Check _ _ (Lambda _ _)) = return TypeError
rules k (Check ctx a (Up t)) = k (Synthesise ctx t) >>= \case
    Synthesised b -> if a == b then return Checked else return TypeError
    _ -> return TypeError

stlc :: MonadicTraversal Question Answer Question Answer
stlc = rules . stlc

typecheck :: Question -> Answer
typecheck q = q & stlc .~ TypeError

-- A test

test :: Answer
test = typecheck $ Synthesise [("x", TVar "a")]
                    $ App (Down (Function (TVar "a") (TVar "a")) (Lambda "y" (Up (Var "y"))))
                      (Up (Var "x"))

-- How do we get to the bidirectional datatypes for STLC?

data STLC where
  SVar :: String -> STLC
  SApp :: STLC -> STLC -> STLC
  SLam :: String -> STLC -> STLC
  SAnn :: Type -> STLC -> STLC

{- First attempt was a dud
stlcSyn :: STLC -> TermSyn
stlcSyn (SVar x) = Var x
stlcSyn (SApp t u) = App (stlcSyn t) (Up (stlcSyn u))
-- This is the problematic case
stlcSyn (SLam x t) = Down (TVar x) (Lambda x (stlcChk t))

stlcChk :: STLC -> TermChk
stlcChk (SLam x t) = Lambda x (stlcChk t)
stlcChk t = Up (stlcSyn t)
-}

stlcSyn :: STLC -> Maybe TermSyn
stlcSyn (SVar x) = return $ Var x
stlcSyn (SApp t u) = App <$> stlcSyn t <*> (Up <$> stlcSyn u)
stlcSyn (SLam _ _) = Nothing
stlcSyn (SAnn a t) = Down a <$> stlcChk a t

stlcChk :: Type -> STLC -> Maybe TermChk
stlcChk (Function _ res) (SLam x t) = Lambda x <$> stlcChk res t
stlcChk _ (SAnn ty t) = stlcChk ty t
stlcChk _ t = Up <$> stlcSyn t

-- The rest of the blog post

{- this turns out not to typecheck. Oh the irony.
plus :: (Functor f)
     => ((a -> f b) -> s -> f t) -> ((a' -> f b') -> s' -> f t')
     -> (Either a a' -> f (Either b b') -> Either s s' -> f (Either t t'))
plus l _ k (Left s) = Left <$> l (fmap (\(Left s) -> s) . k . Left) s
plus _ l' k (Right s') = Right <$> l' (fmap (\(Right s') -> s') . k . Right) s'
-}
data OverallAnswer = ScopeError' | TypeError' | Type Type

data ScopeCheckQuestion = ScopeCheckQuestion
data ScopeCheckAnswer = WellScoped | ScopeError

scopecheck :: MonadicTraversal ScopeCheckQuestion ScopeCheckAnswer
                               ScopeCheckQuestion ScopeCheckAnswer
scopecheck _ ScopeCheckQuestion = undefined

pipeline :: MonadicTraversal (Context, TermSyn)
                             OverallAnswer
                             (Either ScopeCheckQuestion Question)
                             (Either ScopeCheckAnswer Answer)
pipeline k (ctx, t) = k (Left ScopeCheckQuestion) >>= \case
  Left ScopeError -> return ScopeError'
  Left WellScoped -> k (Right (Synthesise ctx t)) >>= \case
    Right TypeError -> return TypeError'
    Right (Synthesised a) -> return (Type a)
    -- AI generated
    {-
    Right Checked -> k $ Right (Check ctx Unit (Up (stlcChk t))) >>= \case
      Right Checked -> return (Type Unit)
      Right TypeError -> return TypeError'
      Right (Synthesised a) -> return (Type a)
-}