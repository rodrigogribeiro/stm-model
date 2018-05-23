{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TupleSections #-}
module STM.Semantics.TL2Semantics (tl2Semantics) where

import qualified Data.Map as Map
import Data.Set (Set)

import STM.Basic.Definitions
import STM.Syntax.Syntax

import STM.Semantics.Basics

-- read operation 

readVal :: Var -> Stamp -> STM (Set Tran)
readVal v st
  = do
      h <- tranHeap
      ws <- writeSet
      rs <- readSet
      case ( lookupHeap v rs
           , lookupHeap v ws
           , lookupHeap v h ) of
        (Just (_,val), Nothing , Just (st', _)) -> 
          if st' <= st then recordRead st v val
            else retry
        (_       , Just (_,val), _)        ->
          recordRead st v val
        (Nothing , Nothing , Just (st',val)) ->
          if st' <= st then
            do { updateReadSet v (st',val)
               ; recordRead st v val }
          else retry
        (Nothing , Nothing, Nothing)   ->
          do { updateWriteSet v (st, Val 0)
             ; _ <- recordWrite st v (Val 0)
             ; recordRead st v (Val 0) }
        (_ , _ , _ )   ->
          error "Impossible!"


-- commit validation test

validate :: ReadSet -> Heap -> Bool
validate (Heap rs) (Heap h)
  = Map.foldrWithKey (\ v (st,val) ac ->
                       cond (h Map.! v) st val && ac) True rs
    where
      cond p st val = fst p <= st && (snd p) == val


-- instantiating the semantics for TL2

tl2Semantics :: Soup -> Trace
tl2Semantics = exec validate readVal
