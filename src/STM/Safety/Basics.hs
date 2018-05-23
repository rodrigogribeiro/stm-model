module STM.Safety.Basics where

import qualified Data.Map as Map

import STM.Basic.Definitions

-- generates a list of all possible completions of a given trace
-- notice that since we do not have commit pending, we just abort all
-- live transactions

completions :: Trace -> [Trace]
completions 
  = foldr abortLives [] . splits
    where
      abortLives tr ac
        | commited tr = tr : ac
        | otherwise = ac  


-- testing if a trace preserves the real time order. We test this
-- by resorting to stamp.

preservesOrder :: Trace -> Bool
preservesOrder tr
  = and [ i <= i' | (p,  i)  <- tr',
                    (p', i') <- tr',
                    p <= p']
    where
      tr' :: [(Int, Stamp)]
      tr' = zipWith step [0..] tr
      step p i = (p,(stampOf i))

-- testing if a transaction is commited

commited :: Trace -> Bool
commited
  = p . last
    where
      p (ICommit _) = True
      p (IAbort _)  = True
      p _           = False
  

-- divides a given trace in traces of just a given transaction

splits :: Trace -> [Trace]
splits
  = Map.elems . foldr step Map.empty
    where
      step i ac
         = maybe (Map.insert (stampOf i) [i] ac)
                 (\ is -> Map.insert (stampOf i)
                                     (i : is)
                                     ac)
                 (Map.lookup (stampOf i) ac)

