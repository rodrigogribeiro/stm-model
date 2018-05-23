module STM.Semantics.STMHaskellSemantics (stmHaskellSemantics) where

import qualified Data.Map as Map
import Data.Set (Set)

import STM.Basic.Definitions
import STM.Syntax.Syntax

import STM.Semantics.Basics

-- reading variables

readVal :: Var -> Stamp -> STM (Set Tran)
readVal v st
  = do
      h <- tranHeap
      ws <- writeSet
      rs <- readSet
      case ( lookupHeap v rs
           , lookupHeap v ws
           , lookupHeap v h ) of
        (_, Just (_,val), _) -> recordRead st v val
        (Just (_,val), Nothing, _) -> recordRead st v val
        (Nothing, Nothing, Just (st',val)) ->
            do { updateReadSet v (st',val)
               ; recordRead st v val }
        (Nothing, Nothing, Nothing) ->
          do { updateWriteSet v (st, Val 0)
             ; _ <- recordWrite st v (Val 0)
             ; recordRead st v (Val 0) }


validate :: ReadSet -> Heap -> Bool
validate (Heap rs) (Heap h)
  = Map.foldrWithKey (\ v (_,val) ac ->
                       cond (h Map.! v) val && ac) True rs
    where
      cond p val = (snd p) == val


stmHaskellSemantics :: Soup -> Trace
stmHaskellSemantics = exec validate readVal
