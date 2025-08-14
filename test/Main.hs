module Main (main) where

import HM.Lang

import qualified HM.Subst as Subst
import qualified HM.UnionFind as UF
import qualified HM.Elab as Elab

import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = do
  defaultMain tests

inferTest :: Term -> Either String Type
inferTest term = case Subst.inferMain term of
  Right (ty, _) -> Right (normalizeType ty)
  Left s -> Left s

tests :: TestTree
tests =
  testGroup "Hindley-Milner Type Inference Tests"
    [ testGroup "Subst"
      [ testCase name $ Right expected @=? inferTest term | (name, term, expected) <- testCases ]
    , testGroup "UnionFind"
      [ testCase name $ do
          res <- UF.inferTest term
          Right expected @=?  res
      | (name, term, expected) <- testCases ]
    , testGroup "System F Elab"
      [ testCase name $ do
          res <- Elab.inferTest term
          Right expected @=?  res
      | (name, term, expected) <- testCases ]
    ]

testCases :: [(String, Term, Type)]
testCases =
  [ ("const Int", Lam "x" (Int 42), TArrow (TypeVar 0) TInt)
  , ("id", Lam "x" (Var "x"), TArrow (TypeVar 0) (TypeVar 0))
  , ("id int app", App (Lam "x" (Var "x")) (Int 42), TInt)
  , ("let id", Let "x" (Lam "y" (Var "y")) (App (Var "x") (Int 42)), TInt)
  , ("let id self app", Let "x" (Lam "y" (Var "y")) (App (App (Var "x") (Var "x")) (Int 1)), TInt)
  , ("let under lambda", Lam "z" (Let "x" (Lam "y" (Var "y")) (App (Var "x") (Var "z"))), TArrow (TypeVar 0) (TypeVar 0))
  , ("nested let", Let "x" (Lam "y" (Var "y")) (Let "z" (Var "x") (App (Var "z") (Int 42))), TInt)
  ]
