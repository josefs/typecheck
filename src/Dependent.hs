module Dependent where

-- An implementation of "An algorithm for type-checking dependent types"
-- by Thierry Coquand in Haskell
-- https://www.sciencedirect.com/science/article/pii/0167642395000216
-- https://core.ac.uk/download/pdf/82345314.pdf

-- The first example of bidirectional typechecking that I'm aware of

type Id = String
data Exp
  = Var Id
  | App Exp Exp
  | Abs Id Exp
  | Let Id Exp Exp Exp
  | Pi Id Exp Exp
  | Type
  deriving Show

data Val = VGen Int | VApp Val Val | VType | VClos Env Exp
  deriving Show
type Env = [(Id,Val)]

update :: Env -> Id -> Val -> Env
update env x v = (x,v):env

-- a short way of writing the whnf algorithm

app :: Val -> Val -> Val
eval :: Env -> Exp -> Val

app (VClos env (Abs x e)) v = eval (update env x v) e
app u v = VApp u v

eval env (Var x) = case lookup x env of
  Just v -> v
  Nothing -> error "variable not found"
eval env (App f a) = app (eval env f) (eval env a)
eval env (Let x e1 _ e3) = eval (update env x (eval env e1)) e3
eval _   Type = VType
eval env e = VClos env e

whnf :: Val -> Val
whnf (VApp u v) = app (whnf u) (whnf v)
whnf (VClos env e) = eval env e
whnf v = v

eqVal :: (Int,Val,Val) -> Bool
eqVal (k, u1, u2) = case (whnf u1, whnf u2) of
  (VType, VType) -> True
  (VApp t1 w1, VApp t2 w2) -> eqVal (k,t1,t2) && eqVal (k,w1,w2)
  (VGen i, VGen j) -> i == j
  (VClos env1 (Abs x1 e1), VClos env2 (Abs x2 e2)) ->
      let v = VGen k
      in eqVal (k,VClos (update env1  x1 v) e1, VClos (update env2 x2 v) e2)
  (VClos env1 (Pi x1 a1 b1), VClos env2 (Pi x2 a2 b2)) ->
      let v = VGen k
      in eqVal (k,VClos env1 a1, VClos env2 a2) &&
         eqVal (k+1,VClos (update env1 x1 v) b1, VClos (update env2 x2 v) b2)
  _ -> False

checkExp :: (Int, Env, Env) -> Exp -> Val -> Bool
inferExp :: (Int,Env,Env) -> Exp -> Val
checkType :: (Int, Env, Env) -> Exp -> Bool

checkType (k, rho, gamma) e = checkExp (k, rho, gamma) e VType

checkExp (k, rho, gamma) e v =
  case e of
    Abs x n ->
      case whnf v of
        VClos env (Pi y a b) ->
          let v' = VGen k
          in checkExp (k+1, update rho x v', update gamma x (VClos env a)) n (VClos (update env y v') b)
        _ -> error "expected a function type"
    Pi x a b ->
      case whnf v of
        VType -> checkType (k, rho, gamma) a && checkType (k+1, update rho x (VGen k), update gamma x (VClos rho a)) b
        _ -> error "expected Type"
    Let x e1 e2 e3 ->
      checkType (k, rho, gamma) e2 &&
      checkExp (k, update rho x (eval rho e1), update gamma x (eval rho e2)) e3 v
    _ -> eqVal (k, inferExp (k, rho, gamma) e,v)

inferExp (k, rho, gamma) e =
  case e of
    Var i -> case lookup i gamma of
      Just v -> v
      Nothing -> error "variable not found"
    App e1 e2 ->
      case inferExp (k, rho, gamma) e1 of
        VClos env (Pi x a b) ->
          if checkExp (k, rho, gamma) e2 (VClos env a)
          then VClos (update env x (VClos rho e2)) b
          else error "application error"
        _ -> error "expected Pi"
    Type -> VType
    _ -> error "cannot infer type"

typecheck :: Exp -> Exp -> Bool
typecheck e t = checkType (0,[],[]) t && checkExp (0,[],[]) e (VClos [] t)

test :: Bool
test = typecheck (Abs "A" (Abs "x" (Var "x")))
  (Pi "A" Type (Pi "x" (Var "A") (Var "A")))
