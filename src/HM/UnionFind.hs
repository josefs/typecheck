{-# LANGUAGE LambdaCase #-}
module HM.UnionFind where

import qualified UnionFindIO as UF
import HM.Lang (Term(..), TermVar)
import qualified HM.Lang as Lang

import Control.Monad.State hiding (liftIO)

import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as Map

import System.IO

-- Types

data Type
  = MetaTypeVar (UF.Var Type)
  | TypeVar String
  | TArrow Type Type
  | TInt

instance Show Type where
  show (MetaTypeVar v) = "MetaTypeVar"
  show (TypeVar v) = "TypeVar " ++ v
  show (TArrow t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show TInt = "Int"

data Scheme
  = Forall [String] Type
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
newMetaTyVar = MetaTypeVar <$> liftIO UF.newVar

debug :: String -> TCM ()
debug msg = liftIO (hPutStrLn stderr msg)

-- Environment

type Env = Map TermVar Scheme

lookupEnv :: TermVar -> Env -> TCM Scheme
lookupEnv x env =
  case Map.lookup x env of
    Just scheme -> return scheme
    Nothing -> TCM $ return $ Left $ "Variable not found: " ++ x

updateEnv :: TermVar -> Scheme -> Env -> Env
updateEnv x scheme env =
  Map.insert x scheme env


--  Working with types

occursCheck :: UF.Var Type -> Type -> TCM ()
occursCheck v (MetaTypeVar v') = TCM $ do
  b <- UF.areEqual v v'
  return $ if b then Left "Occurs check failed" else Right ()
occursCheck v (TypeVar _) = return ()
occursCheck v (TArrow t1 t2) = do
  occursCheck v t1
  occursCheck v t2
occursCheck v TInt = return ()

unify :: Type -> Type -> TCM ()
unify (MetaTypeVar v) ty = do
  payload <- liftIO $ UF.getPayload v
  case payload of
    Just ty' -> unify ty' ty
    Nothing -> do
      occursCheck v ty
      liftIO $ UF.setPayload v ty
unify ty (MetaTypeVar v) = unify (MetaTypeVar v) ty
unify (TypeVar v1) (TypeVar v2) = TCM $ return $
  if v1 == v2 then Right () else Left $ "Type variable mismatch: " ++ v1 ++ " vs " ++ v2
unify (TArrow t1 t2) (TArrow t3 t4) = do
  unify t1 t3
  unify t2 t4
unify TInt TInt = return ()
unify t1 t2 = TCM $ return $ Left $ "Type mismatch: " ++ show t1 ++ " vs " ++ show t2

instantiate :: Scheme -> TCM Type
instantiate (Forall [] ty) = return ty
instantiate (Forall vars ty) = do
  metaVars <- mapM (const newMetaTyVar) vars
  let subst = Map.fromList (zip vars metaVars)
  let applySubst (MetaTypeVar v) = MetaTypeVar v
      applySubst (TypeVar v) =
        case  Map.lookup v subst of
          Just t -> t
          Nothing -> TypeVar v
      applySubst (TArrow t1 t2) = TArrow (applySubst t1) (applySubst t2)
      applySubst TInt = TInt
  return $ applySubst ty

-- Generalization

pathCompressType :: Type -> IO Type
pathCompressType (MetaTypeVar v) = do
  payload <- UF.getPayload v
  case payload of
    Just ty -> do
      pathCompressType ty
    Nothing ->
      MetaTypeVar <$> UF.findRoot v
pathCompressType (TypeVar v) = return $ TypeVar v
pathCompressType (TArrow t1 t2) = TArrow <$> pathCompressType t1 <*> pathCompressType t2
pathCompressType TInt = return TInt

pathCompressScheme :: Scheme -> IO Scheme
pathCompressScheme (Forall vars ty) = do
  ty' <- pathCompressType ty
  return $ Forall vars ty'

freeTypeVars :: Type -> [UF.Var Type]
freeTypeVars (MetaTypeVar v) = [v]
freeTypeVars (TypeVar _) = []
freeTypeVars (TArrow t1 t2) = freeTypeVars t1 ++ freeTypeVars t2
freeTypeVars TInt = []

freeTypeVarsInScheme :: Scheme -> [UF.Var Type]
freeTypeVarsInScheme (Forall vars ty) = freeTypeVars ty

rename :: [(UF.Var Type, String)] -> Type -> Type
rename renames (MetaTypeVar v) =
  case lookup v renames of
    Just name -> TypeVar name
    Nothing -> MetaTypeVar v
rename renames (TypeVar v) = TypeVar v
rename renames (TArrow t1 t2) = TArrow (rename renames t1) (rename renames t2)
rename renames TInt = TInt

generalize :: Env -> Type -> TCM Scheme
generalize env ty = do
  ty' <- liftIO $ pathCompressType ty
  let freeVars = freeTypeVars ty'
  envSchemes <- mapM (liftIO . pathCompressScheme . snd) (Map.toList env)
  let forbiddenVars = concatMap freeTypeVarsInScheme envSchemes
  let genVars = freeVars \\ forbiddenVars
  -- We don't need to generate globally unique names for the variables,
  -- because we don't have nested polymorphism. There's only a single
  -- quantifier at the front of each type scheme.
  let quantVars = ["v" ++ show i | i <- [0..length genVars - 1]]
  let renames = zip genVars quantVars
  let renamedTy = rename renames ty'
  return $ Forall quantVars renamedTy

-- Type inference function

inferType :: Env -> Term -> TCM Type
inferType env (Var x) = do
  scheme <- lookupEnv x env
  instantiate scheme
inferType _env (Int _) = return TInt
inferType env (App t1 t2) = do
  t1Type <- inferType env t1
  t2Type <- inferType env t2
  resType <- newMetaTyVar
  unify t1Type (TArrow t2Type resType)
  return resType
inferType env (Lam x body) = do
  xType <- newMetaTyVar
  let
    newEnv = updateEnv x (Forall [] xType) env
  bodyType <- inferType newEnv body
  return $ TArrow xType bodyType
inferType env (Let x e body) = do
  eType <- inferType env e
  xType <- generalize env eType
  let newEnv = updateEnv x xType env
  inferType newEnv body

inferMain :: Term -> TCM Type
inferMain term = do
  let env = Map.empty :: Env
  ty <- inferType env term
  liftIO $ pathCompressType ty


-- Type inference for tests

inferTest :: Term -> IO (Either String Lang.Type)
inferTest term = do
  eTy <- runTCM (inferMain term)
  case eTy of
    Left err -> return $ Left err
    Right ty -> do
      let renamedTy = toLangTy ty
      return $ Right renamedTy

data Rename = Rename
  { renames :: [(UF.Var Type, Int)]
  , nextName :: Int
  }

toLangTy :: Type -> Lang.Type
toLangTy ty = evalState (toLangType ty) (Rename [] 0)

toLangType :: Type -> State Rename Lang.Type
toLangType (MetaTypeVar v) = do
  renameSt <- get
  case lookup v (renames renameSt) of
    Just n -> return $ Lang.TypeVar n
    Nothing -> do
      let newName = nextName renameSt
      put $ Rename ((v, newName) : renames renameSt) (newName + 1)
      return $ Lang.TypeVar newName
toLangType (TypeVar _) = error "toLangType should not be applied to type scheme"
toLangType (TArrow t1 t2) =
  Lang.TArrow <$> toLangType t1 <*> toLangType t2
toLangType TInt = return Lang.TInt