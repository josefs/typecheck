module UnionFindIO where

import Data.IORef
import Control.Monad (when)
import Control.Applicative ((<|>))

newtype Var a = Var { getRef :: IORef (Node a) }
  deriving Eq

data Node a
  = Root (Maybe a) Int  -- Payload and rank
  | Link (Var a)  -- Pointer to another variable
  deriving Eq

newVar :: IO (Var a)
newVar = do
  ref <- newIORef (Root Nothing 0)
  return (Var ref)

findRoot :: Var a -> IO (Var a)
findRoot var@(Var ref) = do
  node <- readIORef ref
  case node of
    Root _ _ -> return var
    Link parent -> do
      root <- findRoot parent
      writeIORef ref (Link root)  -- Path compression
      return root

unionVars :: Var a -> Var a -> IO ()
unionVars var1 var2 = do
  root1 <- findRoot var1
  root2 <- findRoot var2
  when (root1 /= root2) $ do
    let Var ref1 = root1
        Var ref2 = root2
    node1 <- readIORef ref1
    node2 <- readIORef ref2
    case (node1, node2) of
      (Root (Just _) _, Root (Just _) _) ->
        error "Cannot union variables with payloads"
      (Root payload1 rank1, Root payload2 rank2)
        | rank1 > rank2 -> writeIORef ref2 (Link root1)
        | rank1 < rank2 -> writeIORef ref1 (Link root2)
        | otherwise -> do
            let payload = payload1 <|> payload2
            writeIORef ref2 (Link root1)
            writeIORef ref1 (Root payload (rank1 + 1))

areEqual :: Var a -> Var a -> IO Bool
areEqual var1 var2 = do
  root1 <- findRoot var1
  root2 <- findRoot var2
  return (root1 == root2)

getPayload :: Var a -> IO (Maybe a)
getPayload var = do
  root <- findRoot var
  node <- readIORef (getRef root)
  case node of
    Root payload _ -> return payload
    Link _ -> return Nothing  -- No payload if it's a link

setPayload :: Var a -> a -> IO ()
setPayload var payload = do
  root <- findRoot var
  let ioVar  = getRef root
  node <- readIORef ioVar
  case node of
    Root (Just _) _ -> error "Cannot set payload on a variable that already has a payload"
    Root _ rank -> writeIORef ioVar (Root (Just payload) rank)
    Link _ -> error "Cannot happen"