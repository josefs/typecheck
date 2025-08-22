module Main (main) where

import HM.Lang

import qualified HM.Subst as Subst
import qualified HM.UnionFind as UF
import qualified HM.Elab as Elab
import qualified HM.LevelEager as LE

import Test.Tasty
import Test.Tasty.HUnit
import Data.Either (Either)

main :: IO ()
main = do
  defaultMain tests

hmTestGroup :: String -> (Term -> IO (Either String Type)) -> [(String, Term, Type)] -> TestTree
hmTestGroup groupName inferFunc testCases =
  testGroup groupName
    [ testCase name $ do
        res <- inferFunc term
        Right expected @=?  res
    | (name, term, expected) <- testCases ]

tests :: TestTree
tests =
  testGroup "Hindley-Milner Type Inference Tests" $
  map ($ testCases)
    [ hmTestGroup "Subst" Subst.inferTest
    , hmTestGroup "UnionFind" UF.inferTest
    , hmTestGroup "System F Elab" Elab.inferTest
    , hmTestGroup "Level Eager" LE.inferTest
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
