{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module HM.LevelEager where

-- A port of https://okmij.org/ftp/ML/generalization/sound_eager.ml

import qualified HM.Lang as Lang
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class

import System.IO.Unsafe (unsafePerformIO)

type Level = Int

type TypeVar = String

data Type
  = MetaTyVar (IORef TV)
  | TyVar TypeVar
  | TyArrow Type Type
  | TyInt
  deriving (Eq)

data TV
  = Unbound TypeVar Level
  | Link Type

instance Show Type where
  show (MetaTyVar ref) = "MetaTyVar" ++ unsafePerformIO (do
    mNode <- readIORef ref
    case mNode of
      Unbound name lvl -> return ("(" ++ name ++ ", " ++ show lvl ++ ")")
      Link t -> return (show t))
  show (TyVar v) = "TypeVar " ++ v
  show (TyArrow t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show TyInt = "Int"

-- Typechecking Monad

newtype TCM a = TCM { runTCM :: StateT (Level, Int) (ExceptT String IO) a }
  deriving (Functor, Applicative, Monad)

instance MonadFail TCM where
  fail msg = TCM (lift (throwE msg))

liftIO :: IO a -> TCM a
liftIO io = TCM (lift (lift io))

newMetaTyVar :: TCM Type
newMetaTyVar = do
  (lvl,name) <- TCM get
  let varName = "meta" ++ show name
  ref <- liftIO (newIORef (Unbound varName lvl))
  return (MetaTyVar ref)

increaseLevel :: TCM ()
increaseLevel = do
  (level,nm) <- TCM get
  TCM $ put (level + 1, nm)

decreaseLevel :: TCM ()
decreaseLevel = do
  (level, nm) <- TCM get
  TCM $ put (level - 1, nm)

greaterThanCurrentLevel :: Level -> TCM Bool
greaterThanCurrentLevel lvl = do
  (currentLevel, _) <- TCM get
  return (lvl > currentLevel)

debug :: String -> TCM ()
debug msg = do
  (level,_) <- TCM get
  liftIO (putStrLn ("[Level " ++ show level ++ "] " ++ msg))

-- Working with types

occursCheck :: IORef TV -> Type -> TCM ()
occursCheck ref (MetaTyVar mRef) | ref == mRef = fail "Occurs check failed"
occursCheck ref (MetaTyVar mRef) = do
  mNode <- liftIO (readIORef mRef)
  case mNode of
    Unbound name lvl -> do
      tvr <- liftIO (readIORef ref)
      -- Set minimum level for the meta type variable
      case tvr of
        Unbound _ lvl' -> when (lvl' < lvl) $ do
          liftIO (writeIORef mRef (Unbound name lvl'))
        Link _ -> return ()
    Link t -> occursCheck ref t
occursCheck _ (TyVar _) = return ()
occursCheck ref (TyArrow t1 t2) = do
  occursCheck ref t1
  occursCheck ref t2
occursCheck _ TyInt = return ()

unify :: Type -> Type -> TCM ()
unify (MetaTyVar mRef) t = do
  tv <- liftIO $ readIORef mRef
  case tv of
    Unbound _ _-> do
      occursCheck mRef t
      liftIO (writeIORef mRef (Link t))
    Link t' -> unify t' t
unify t (MetaTyVar mRef) = unify (MetaTyVar mRef) t
unify (TyArrow t1 t2) (TyArrow t1' t2') = do
  unify t1 t1'
  unify t2 t2'
unify TyInt TyInt = return ()
unify (TyVar v1) (TyVar v2)
  | v1 == v2 = return ()
  | otherwise = fail $ "Cannot unify different type variables: " ++ v1 ++ " and " ++ v2
unify t1 t2 = fail $ "Type mismatch: " ++ show t1 ++ " vs " ++ show t2

-- Environment

type Env = Map Lang.TermVar Type

-- Generalization

generalize :: Type -> TCM Type
generalize (MetaTyVar mRef) = do
  tv <- liftIO $ readIORef mRef
  case tv of
    Unbound varName lvl -> do
      b <- greaterThanCurrentLevel lvl
      if b then
        return (TyVar varName)
        else return (MetaTyVar mRef)
    Link t -> generalize t
generalize (TyArrow t1 t2) = do
  t1' <- generalize t1
  t2' <- generalize t2
  return (TyArrow t1' t2')
generalize ty = return ty

-- Instantiation

instantiate :: Type -> TCM Type
instantiate ty = do
  let
    loop subst (TyVar v) = case Map.lookup v subst of
      Just t -> return (t, subst)
      Nothing -> do
        tv <- newMetaTyVar
        return (tv, Map.insert v tv subst)
    loop subst (MetaTyVar mRef) = do
      tv <- liftIO $ readIORef mRef
      case tv of
        Unbound _ _ -> return (MetaTyVar mRef, subst)
        Link t -> loop subst t
    loop subst (TyArrow t1 t2) = do
      (t1', subst1) <- loop subst t1
      (t2', subst2) <- loop subst1 t2
      return (TyArrow t1' t2', subst2)
    loop subst TyInt = return (TyInt, subst)
  (instTy, _) <- loop Map.empty ty
  return instTy

typeof :: Env -> Lang.Term -> TCM Type
typeof env (Lang.Var x) =
  case Map.lookup x env of
    Just ty -> instantiate ty
    Nothing -> fail $ "Variable not found: " ++ x
typeof env (Lang.App e1 e2) = do
  ty1 <- typeof env e1
  ty2 <- typeof env e2
  res <- newMetaTyVar
  unify ty1 (TyArrow ty2 res)
  return res
typeof env (Lang.Lam x e) = do
  res <- newMetaTyVar
  let env' = Map.insert x res env
  ty <- typeof env' e
  return (TyArrow res ty)
typeof env (Lang.Let x e1 e2) = do
  increaseLevel
  ty1 <- typeof env e1
  decreaseLevel
  genTy <- generalize ty1
  let env' = Map.insert x genTy env
  typeof env' e2
typeof _env (Lang.Int _) = return TyInt

-- Main type inference function

inferMain :: Lang.Term -> TCM Type
inferMain term = do
  let env = Map.empty :: Env
  typeof env term

inferTest :: Lang.Term -> IO (Either String Lang.Type)
inferTest term = do
  result <- runExceptT (runStateT (runTCM (inferMain term)) (0,0))
  case result of
    Left err -> return (Left err)
    Right (ty, _) -> do
      -- Normalize the type before returning it
      zonkedTy <- zonk ty
      let normalizedTy = toLangTy zonkedTy
      return (Right normalizedTy)

zonk :: Type -> IO Type
zonk (MetaTyVar mRef) = do
  mNode <- readIORef mRef
  case mNode of
    Unbound _ _ -> return (MetaTyVar mRef)
    Link t -> zonk t
zonk (TyVar v) = return (TyVar v)
zonk (TyArrow t1 t2) = do
  t1' <- zonk t1
  t2' <- zonk t2
  return (TyArrow t1' t2')
zonk TyInt = return TyInt

data Rename = Rename
  { renames :: [(IORef TV, Int)]
  , nextName :: Int
  }

toLangTy :: Type -> Lang.Type
toLangTy ty = evalState (toLangType ty) (Rename [] 0)

toLangType :: Type -> State Rename Lang.Type
toLangType (MetaTyVar v) = do
  renameSt <- get
  case lookup v (renames renameSt) of
    Just n -> return $ Lang.TypeVar n
    Nothing -> do
      let newName = nextName renameSt
      put $ Rename ((v, newName) : renames renameSt) (newName + 1)
      return $ Lang.TypeVar newName
toLangType (TyVar _) = error "toLangType should not be applied to type scheme"
toLangType (TyArrow t1 t2) =
  Lang.TArrow <$> toLangType t1 <*> toLangType t2
toLangType TyInt = return Lang.TInt