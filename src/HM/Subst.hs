{-# LANGUAGE TupleSections #-}

{-
This module implements the Hindley-Milner type system
using explicit substitutions.

This is a bad idea. It's hard to keep track of when to apply substitutions,
and it's easy to miss applying them in various places.
Factoring out the substitution into a union find module is
definitely a good idea.
-}

module HM.Subst where

import HM.Lang

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

data TypeScheme
  = Forall [TyVar] Type
  deriving (Show, Eq)

type Subst = Map TyVar Type

type Env = Map TermVar TypeScheme


lookupType :: Env -> TermVar -> Either String TypeScheme
lookupType env v =  maybe (Left $ "Unknown variable: " ++ v) Right $ Map.lookup v env

combineSubst :: Subst -> Subst -> Subst
combineSubst =
  Map.unionWithKey (\k t1 t2 ->
    error $ "Variable " ++ show k ++ "assigned to both " ++ show t1 ++ " and " ++ show t2)

-- Do the types need to be substituted before equating them?
-- I guess so, how else would we detect cycles?
eqType :: Type -> Type -> Either String Subst
eqType (TypeVar v1) ty | occurs v1 ty
  = Left $ "Type variable occurs in type: " ++ show v1 ++ " in " ++ show ty
eqType (TypeVar v1) ty = return (Map.singleton v1 ty)
eqType ty tv@(TypeVar v2) = eqType tv ty
eqType TInt TInt = return Map.empty
eqType (TArrow t1 t2) (TArrow t3 t4) = do
  subst1 <- eqType t1 t3
  subst2 <- eqType (applySubst subst1 t2) (applySubst subst1 t4)
  return (Map.union subst1 subst2)
eqType t1 t2 = Left $ "Type mismatch: " ++ show t1 ++ " vs " ++ show t2

applySubst :: Subst -> Type -> Type
applySubst subst tv@(TypeVar v) = case Map.lookup v subst of
  Just t -> applySubst subst t
  Nothing -> tv
applySubst subst TInt = TInt
applySubst subst (TArrow t1 t2) = TArrow (applySubst subst t1) (applySubst subst t2)

applySubstScheme :: Subst -> TypeScheme -> TypeScheme
applySubstScheme subst (Forall vars ty) =
  let
    newSubst = Map.filterWithKey (\v _ -> v `notElem` vars) subst
    ty' = applySubst newSubst ty
  in
    Forall vars ty'

freeTypeVars :: Type -> Set TyVar
freeTypeVars (TypeVar v) = Set.singleton v
freeTypeVars TInt = Set.empty
freeTypeVars (TArrow t1 t2) = Set.union (freeTypeVars t1) (freeTypeVars t2)

freeTypeVarsInScheme :: TypeScheme -> Set TyVar
freeTypeVarsInScheme (Forall vars ty) =
  let
    allVars = Set.fromList vars
    freeVars = freeTypeVars ty
  in
    Set.difference freeVars allVars

generalize :: Type -> Env -> Subst -> TypeScheme
generalize ty env subst =
  let
    forbiddenVars = Set.unions $ map (freeTypeVarsInScheme . applySubstScheme subst) $ Map.elems env
    ty' = applySubst subst ty
    vars = freeTypeVars ty'
    genVars = Set.toList $ Set.difference vars forbiddenVars
  in
    Forall genVars ty

instantiate :: TypeScheme -> Int -> (Type, Int)
instantiate (Forall [] t) name = (t, name)
instantiate (Forall vars t) name = (applySubst subst t, newName)
  where
    newName = name + length vars
    subst = Map.fromList (zip vars (map TypeVar [name..]))

occurs :: TyVar -> Type -> Bool
occurs v (TypeVar v') = v == v'
occurs v (TArrow t1 t2) = occurs v t1 || occurs v t2
occurs _ TInt = False

infer :: Env -> Subst -> Int -> Term -> Either String (Type, Subst, Int)
infer env subst v (Var x) = do
  scheme <- lookupType env x
  let (ty,v') = instantiate scheme v
  return (ty, subst, v')
infer env subst v (Int _) = return (TInt,subst,v)
infer env subst v (App t1 t2) = do
  (t1Type,subst1,v1) <- infer env subst v t1
  (t2Type,subst2,v2) <- infer env subst1 v1 t2
  let
      retType = TypeVar v2
      t1Type' = applySubst subst2 t1Type
  subst3 <- eqType t1Type' (TArrow t2Type retType)
  let
    newSubst = combineSubst subst2 subst3
  return (retType, newSubst, v2 + 1)
infer env subst v (Lam x body) = do
  let v1 = v + 1
  let newTyVar = TypeVar v
  let newEnv = Map.insert x (Forall [] newTyVar) env
  (bodyType, subst', v2) <- infer newEnv subst v1 body
  let arrowType = TArrow newTyVar bodyType
  return (arrowType, subst', v2)
infer env subst v (Let x val body) = do
  (valType, subst1, v1) <- infer env subst v val
  let
    genType = generalize valType env subst1
    newEnv = Map.insert x genType env
  (bodyType, subst2, v2) <- infer newEnv subst1 v1 body
  return (bodyType, subst2, v2)

inferMain :: Term -> Either String (Type, Subst)
inferMain term = do
  let env = Map.empty :: Env
  let subst = Map.empty :: Subst
  (ty, subst', _) <- infer env subst 0 term
  return (applySubst subst' ty, subst')