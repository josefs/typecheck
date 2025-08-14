{-# LANGUAGE LambdaCase #-}
module HM.Elab where

import qualified HM.Lang as Lang
import qualified UnionFindIO as UF

import Control.Monad.State hiding (liftIO)

import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as Map

import System.IO
import Control.Monad (when)

-- Lesson learned:
-- * Ditching the notion of type schemes simplifies things a bit. I definitely prefer this.
-- * Dealing with full System F makes other things more complicated, naturally.
-- * We can no longer rely on the trick to only generate local names when generalizing.
--   Terms become non-well-formed if we do that. I've left it in for now, but the current
--   implementation is not sound. The Monad needs to have a global name generator.
-- * The terms are not well-formed for other reasons as well, but I'll leave it for now.
-- * There's a bug where generalization generates more quantifiers than necessary.

-- I have a bespoke type for Type and Term here. I tried to parameterize it on the
-- meta type variable, but it was too much of a hassle to get the code to work.
type TypeVar = String

data Type
  = TyVar TypeVar
  | TyArrow Type Type
  | TyForall String Type
  | MetaTyVar (UF.Var Type)
  | TyInt

type TermVar = String

data Term
  = Var TermVar
  | Int Int
  | App Term Term
  | Lam TermVar Type Term
  | TyLam String Term
  | TyApp Term Type
  | Let TermVar Type Term Term

instance Show Type where
  show (MetaTyVar _) = "MetaTyVar"
  show (TyVar v) = "TypeVar " ++ v
  show (TyArrow t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show TyInt = "Int"
  show (TyForall var ty) = "forall " ++ var ++ ". " ++ show ty

{-
data Scheme = Forall [String] Type
  deriving (Show, Eq)
-}

-- Typechecking Monad

newtype TCM a = TCM { runTCM :: IO (Either String a) }

liftIO :: IO a -> TCM a
liftIO io = TCM (fmap Right io)

instance Functor TCM where
  fmap f (TCM io) = TCM (fmap (fmap f) io)

instance Applicative TCM where
  pure x = TCM (pure (Right x))
  TCM ioF <*> TCM ioX = TCM (ioF >>= \case
    Left err -> pure (Left err)
    Right f -> fmap (fmap f) ioX)

instance Monad TCM where
  TCM io >>= f = TCM (io >>= \case
    Left err -> pure (Left err)
    Right x -> let TCM io' = f x in io')

instance MonadFail TCM where
  fail msg = TCM (pure (Left msg))

newMetaTyVar :: TCM Type
newMetaTyVar = MetaTyVar <$> liftIO UF.newVar

varsEqual :: UF.Var Type -> UF.Var Type -> TCM Bool
varsEqual v1 v2 = liftIO $ UF.areEqual v1 v2

debug :: String -> TCM ()
debug msg = liftIO (hPutStrLn stderr msg)

-- Environment

--type Env = Map TermVar Scheme
type Env = Map TermVar Type

lookupEnv :: TermVar -> Env -> TCM Type
lookupEnv x env =
  case Map.lookup x env of
    Just scheme -> return scheme
    Nothing -> TCM $ return $ Left $ "Variable not found: " ++ x

updateEnv :: TermVar -> Type -> Env -> Env
updateEnv x scheme env =
  Map.insert x scheme env

-- Working with types

occursCheck :: UF.Var Type -> Type -> TCM ()
occursCheck v (MetaTyVar v') = do
  b <- varsEqual v v'
  when b $ fail "Occurs check failed"
occursCheck _ (TyVar _) = return ()
occursCheck v (TyArrow t1 t2) = do
  occursCheck v t1
  occursCheck v t2
occursCheck _ TyInt = return ()
occursCheck v (TyForall _ ty) = occursCheck v ty

unify :: Type -> Type -> TCM ()
unify (MetaTyVar v) ty = do
  payload <- liftIO $ UF.getPayload v
  case payload of
    Just ty' -> unify ty' ty
    Nothing -> do
      occursCheck v ty
      liftIO $ UF.setPayload v ty
unify ty (MetaTyVar v) = unify (MetaTyVar v) ty
unify (TyVar v1) (TyVar v2) =
  if v1 == v2 then pure () else fail $ "Type variable mismatch: " ++ v1 ++ " vs " ++ v2
unify (TyArrow t1 t2) (TyArrow t3 t4) = do
  unify t1 t3
  unify t2 t4
unify TyInt TyInt = return ()
unify t1@(TyForall _ _) t2@(TyForall _ _) =
  fail $ "Forall types should never be unified: " ++ show t1 ++ " vs " ++ show t2
unify t1 t2 = fail $ "Type mismatch: " ++ show t1 ++ " vs " ++ show t2

instantiate :: Type -> Term -> TCM (Term, Type)
instantiate ty term = instantiateHelp ty term []

instantiateHelp :: Type -> Term -> [(String, Type)] -> TCM (Term, Type)
instantiateHelp (TyForall var ty) term subst = do
  metaVar <- newMetaTyVar
  instantiateHelp ty (TyApp term metaVar) ((var,metaVar):subst)
instantiateHelp ty term subst = do
  let
      applySubst (MetaTyVar v) = MetaTyVar v
      applySubst (TyVar v) = case lookup v subst of
        Just ty' -> ty'
        Nothing -> TyVar v
      applySubst (TyArrow t1 t2) = TyArrow (applySubst t1) (applySubst t2)
      applySubst TyInt = TyInt
      applySubst (TyForall var fty) = TyForall var (applySubst fty)
  return (term, applySubst ty) -- TODO: rename the term

-- Generalization

pathCompressType :: Type -> IO Type
pathCompressType (MetaTyVar v) = do
  payload <- UF.getPayload v
  case payload of
    Just ty -> do
      pathCompressType ty
    Nothing ->
      MetaTyVar <$> UF.findRoot v
pathCompressType (TyVar v) = return $ TyVar v
pathCompressType (TyArrow t1 t2) = TyArrow <$> pathCompressType t1 <*> pathCompressType t2
pathCompressType TyInt = return TyInt
pathCompressType (TyForall var ty) = do
  ty' <- pathCompressType ty
  return $ TyForall var ty'

freeTypeVars :: Type -> [UF.Var Type]
freeTypeVars (MetaTyVar v) = [v]
freeTypeVars (TyVar _) = []
freeTypeVars (TyArrow t1 t2) = freeTypeVars t1 ++ freeTypeVars t2
freeTypeVars TyInt = []
freeTypeVars (TyForall _ ty) = freeTypeVars ty

rename :: [(UF.Var Type, String)] -> Type -> Type
rename subst (MetaTyVar v) =
  case lookup v subst of
    Just name -> TyVar name
    Nothing -> MetaTyVar v
rename _subst (TyVar v) = TyVar v
rename subst (TyArrow t1 t2) = TyArrow (rename subst t1) (rename subst t2)
rename _subst TyInt = TyInt
rename subst (TyForall var ty) =
  if var `elem` map snd subst
  then
    error "generalization failed!" -- This shouldn't happen.
  else
    TyForall var (rename subst ty)

-- TODO: Generates too many quantifiers.
generalize :: Env -> Type -> Term -> TCM (Type, Term)
generalize env ty term = do
  ty' <- liftIO $ pathCompressType ty
  let freeVars = freeTypeVars ty'
  envTypes <- mapM (liftIO . pathCompressType . snd) (Map.toList env)
  let forbiddenVars = concatMap freeTypeVars envTypes
  let genVars = freeVars \\ forbiddenVars
  -- We don't need to generate globally unique names for the variables,
  -- because we don't have nested polymorphism. There's only a single
  -- quantifier at the front of each type scheme.
  let quantVars = ["v" ++ show i | i <- [0..length genVars - 1]]
  let subst = zip genVars quantVars
  let renamedTy = rename subst ty'
  let quantTy = foldr TyForall renamedTy quantVars
  let quantTerm = foldr TyLam term quantVars
  return (quantTy, quantTerm)

-- Type inference and elaboration

elabTerm :: Env -> Lang.Term -> TCM (Term, Type)
elabTerm env (Lang.Var x) = do
  ty <- lookupEnv x env
  instantiate ty (Var x)
elabTerm _env (Lang.Int n) = return (Int n, TyInt)
elabTerm env (Lang.App t1 t2) = do
  (f, ty1) <- elabTerm env t1
  (a, ty2) <- elabTerm env t2
  resTy <- newMetaTyVar
  unify ty1 (TyArrow ty2 resTy)
  return (App f a, resTy)
elabTerm env (Lang.Lam x body) = do
  xType <- newMetaTyVar
  let env' = updateEnv x xType env
  (bodyTerm, bodyType) <- elabTerm env' body
  return (Lam x xType bodyTerm, TyArrow xType bodyType)
elabTerm env (Lang.Let x e body) = do
  (eTerm, eType) <- elabTerm env e
  (xType, genTerm) <- generalize env eType eTerm
  let env' = updateEnv x xType env
  (bodyTerm, bodyType) <- elabTerm env' body
  return (Let x xType genTerm bodyTerm, bodyType)

elabMain :: Lang.Term -> TCM (Term, Type)
elabMain term = do
  let env = Map.empty :: Env
  (eTerm, ty) <- elabTerm env term
  -- Normalize the type before returning it
  normalizedTy <- liftIO $ pathCompressType ty
  normalizedTerm <- liftIO $ pathCompressTerm eTerm
  return (normalizedTerm, normalizedTy)

pathCompressTerm :: Term -> IO Term
pathCompressTerm (Var x) = return (Var x)
pathCompressTerm (Int n) = return (Int n)
pathCompressTerm (App t1 t2) = do
  t1' <- pathCompressTerm t1
  t2' <- pathCompressTerm t2
  return (App t1' t2')
pathCompressTerm (Lam x ty body) = do
  ty' <- pathCompressType ty
  body' <- pathCompressTerm body
  return (Lam x ty' body')
pathCompressTerm (TyLam var body) = do
  body' <- pathCompressTerm body
  return (TyLam var body')
pathCompressTerm (TyApp t ty) = do
  t' <- pathCompressTerm t
  ty' <- pathCompressType ty
  return (TyApp t' ty')
pathCompressTerm (Let x ty gen body) = do
  ty' <- pathCompressType ty
  gen' <- pathCompressTerm gen
  body' <- pathCompressTerm body
  return (Let x ty' gen' body')

-- Test functions

inferTest :: Lang.Term -> IO (Either String Lang.Type)
inferTest term = do
  res <- runTCM $ elabMain term
  case res of
    Left err -> return $ Left err
    Right (_, ty) -> do
      let langType = toLangTy ty
      return $ Right langType

data Rename = Rename
  { renames :: [(UF.Var Type, Int)]
  , nextName :: Int
  }

toLangTy :: Type -> Lang.Type
toLangTy ty = evalState (toLangType ty) (Rename [] 0)

-- This will only be applied on the top level type,
-- so we don't need to worry about quantifiers.
toLangType :: Type -> State Rename Lang.Type
toLangType (MetaTyVar v) = do
  renameSt <- get
  case lookup v (renames renameSt) of
    Just n -> return $ Lang.TypeVar n
    Nothing -> do
      let newName = nextName renameSt
      put (renameSt { renames = (v, newName) : renames renameSt, nextName = newName + 1 })
      return $ Lang.TypeVar newName
toLangType (TyVar _) = error "toLangType should not be applied to type scheme"
toLangType (TyArrow t1 t2) = do
  t1' <- toLangType t1
  t2' <- toLangType t2
  return $ Lang.TArrow t1' t2'
toLangType TyInt = return Lang.TInt
toLangType (TyForall _ _) = error "toLangType should not be applied to type scheme"
