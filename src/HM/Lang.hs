module HM.Lang where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Control.Monad.State

-- Untyped terms
data Term
  = Var TermVar
  | App Term Term
  | Lam TermVar Term
  | Let TermVar Term Term
  | Int Int
  deriving (Show, Eq)

type TermVar = String

data Type
  = TInt
  | TArrow Type Type
  | TypeVar TyVar
  deriving (Show, Eq)

type TyVar = Int

normalizeType :: Type -> Type
normalizeType ty = evalState (normTy ty) (NormState IntMap.empty 0)

data NormState = NormState
  { tyVarSubst :: IntMap TyVar
  , nextVar :: Int
  }

normTy :: Type -> State NormState Type
normTy (TArrow t1 t2) = do
  t1' <- normTy t1
  t2' <- normTy t2
  return (TArrow t1' t2')
normTy (TypeVar v) = do
  NormState subst nextVar <- get
  case IntMap.lookup v subst of
    Just v' -> return (TypeVar v')
    Nothing -> do
      let newVar = nextVar
      put (NormState (IntMap.insert v newVar subst) (newVar + 1))
      return (TypeVar newVar)
normTy TInt = return TInt