module HMElab where

-- An implementation of "Hindley-Milner Elaboration in Applicative Style"
-- by François Pottier
-- https://cambium.inria.fr/~fpottier/publis/fpottier-elaboration.pdf


-- Untyped terms
data Term
  = Var TermVar
  | App Term Term
  | Lam TermVar Term
  | Let TermVar Term Term
  deriving (Show, Eq)

type TermVar = String

-- System F types

data Type a b
  = TyVar a
  | TyArrow (Type a b) (Type a b)
  | TyProduct (Type a b) (Type a b)
  | TyForall b (Type a b)
  | TyMu b (Type a b)
  deriving (Show, Eq)

type TyVar = Int
type NominalType = Type TyVar TyVar

-- System F terms

data TermF a b
  = VarF TermVar
  | LamF TermVar (Type a b) (TermF a b)
  | AppF (TermF a b) (TermF a b)
  | LetF TermVar (TermF a b) (TermF a b)
  | TyAbsF b (TermF a b)
  | TyAppF (TermF a b) (Type a b)
  deriving (Show, Eq)

type NominalTerm = TermF TyVar TyVar

ftyabs vs t = foldr TyAbsF vs t
ftyapp t tys = foldl TyAppF t tys

-- Type checking

-- hasType :: Term -> Variable -> Constraint NominalTerm

-- Raw constraints

data RawConstraint
  = CTrue
  | CConj RawConstraint RawConstraint
  | CEq Variable Variable
  | CExist Variable RawConstraint
  | CInstance TermVar Variable [Variable] -- TODO: add ref here
  | CDef TermVar Variable RawConstraint
  | CLet [(TermVar, Variable, Ischeme)] -- TODO: add ref here
    RawConstraint
    RawConstraint
    [Variable] -- TODO: add ref here
  deriving (Show, Eq)

type Variable = Int
