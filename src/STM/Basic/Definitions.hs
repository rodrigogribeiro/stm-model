{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
module STM.Basic.Definitions where

import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as Map

-- stamp for counting commits in TL2 semantics

newtype Stamp = Stamp { unStamp :: Int }
                deriving (Eq, Ord, Show)

-- variable definition

newtype Var = Var { unVar :: Int }
              deriving (Eq, Ord)

instance Show Var where
  show (Var v) = "x_" ++ show v

-- id definition

newtype Id = Id { unId :: Int }
             deriving (Eq, Ord)

instance Show Id where
  show (Id v) = "#" ++ show v

-- value definition

newtype Val = Val { unVal :: Int }
              deriving (Eq, Ord)

instance Show Val where
  show = show . unVal

op :: Val -> Val -> Val
(Val v) `op` (Val v')  = Val (v + v')

-- heap and its operations

newtype Heap = Heap { unHeap :: Map Var (Stamp, Val) }
               deriving (Eq, Ord, Show)

emptyHeap :: Heap
emptyHeap = Heap Map.empty

insertHeap :: Var -> Stamp -> Val -> Heap -> Heap
insertHeap v s val = Heap . Map.insert v (s,val) . unHeap

lookupHeap :: Var -> Heap -> Maybe (Stamp, Val)
lookupHeap v = Map.lookup v . unHeap

unionHeap :: Heap -> Heap -> Heap
unionHeap (Heap h) (Heap h')
  = Heap (h `Map.union` h')

isSubHeapOf :: Heap -> Heap -> Bool
isSubHeapOf (Heap h) (Heap h')
  = h `Map.isSubmapOf` h'

intersectionHeap :: Heap -> Heap -> Heap
intersectionHeap (Heap h) (Heap h')
  = Heap (h `Map.intersection` h')

-- read and write sets

type ReadSet = Heap

type WriteSet = Heap

-- Itens for building traces

data Item = IRead Stamp Var Val
          | IWrite Stamp Var Val
          | IBegin Stamp
          | ICommit Stamp
          | IAbort Stamp
          deriving (Eq, Ord, Show)

type Trace = [Item]

stampOf :: Item -> Stamp
stampOf (IRead i _ _) = i
stampOf (IWrite i _ _) = i
stampOf (IBegin i) = i
stampOf (ICommit i) = i
stampOf (IAbort i) = i

readOrWrite :: Item -> Maybe (Var,Item)
readOrWrite i@(IRead _ v _)
  = Just (v,i)
readOrWrite i@(IWrite _ v _)
  = Just (v,i)
readOrWrite _
  = Nothing


-- getting transaction id

tranId :: MonadReader (Stamp,b) m => m Stamp
tranId = asks fst


-- acess heap (read only)

tranHeap :: MonadReader (a, Heap) m => m Heap
tranHeap
  = asks snd
