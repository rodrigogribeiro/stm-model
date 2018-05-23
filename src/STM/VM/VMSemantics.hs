{-# OPTIONS_GHC -Wall #-}

module STM.VM.VMSemantics where

import Control.Monad (when)
import Control.Arrow (first, second)
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer

import Data.Set (Set)
import qualified Data.Set as Set

import STM.Basic.Definitions
import STM.VM.Instruction


-- stack definition

data StkCell
    = SVal Val
    | Han Code
      deriving (Eq, Ord, Show)

type Stack = [StkCell] 

handler :: Stack -> Code -> (Code, Stack)
handler [] c
  = (c,[])
handler (SVal _ : s) c
  = handler s c
handler (Han c' : s) c
  = (c{nexts = (nexts c') ++ (nexts c)}, s)
 
skip :: Code -> Code
skip c
  = Code (executed c) (skip' (nexts c))
    where
      skip' [] = []
      skip' (Unmark : nx) = nx
      skip' (Mark _ : nx) = skip' (skip' nx)
      skip' (_ : nx) = skip' nx

appM :: ( Monad m
        , Ord b ) => (a -> b) -> m (Set a) -> m (Set b)
f `appM` m
  = (f `Set.map`) <$> m

unionM :: ( Monad m
          , Ord a  ) =>
          m (Set a) -> m (Set a) -> m (Set a)
s `unionM` s1
  = do
      s' <- s
      s1' <- s1
      return (s' `Set.union` s1')

sing :: Monad m => a -> m (Set a)
sing = return . Set.singleton
        
-- Thread stuff

type Thread = (Code, Stack, ReadSet, WriteSet)

type VM a = WriterT Trace (StateT Stamp Identity) a

runVM :: [Thread] -> Heap -> Trace --((Set (Heap, Stack), Trace), Stamp)
runVM ts h = snd $ fst $ runIdentity (runStateT (runWriterT (exec (h,ts))) (Stamp 0))

stepVM :: Heap -> [Thread] -> VM (Set (Heap,[Thread]))
stepVM _ []
  = return Set.empty
stepVM h (t : ts)
  = (second (t :) `appM` stepVM h ts) `unionM` stepThread t h ts

recordBegin :: VM ()
recordBegin
  = get >>= tell . (: []) . IBegin

recordRead :: Var -> Val -> VM ()
recordRead v val
  = do
     st <- get
     tell [ IRead st v val ]


recordWrite :: Var -> Val -> VM ()
recordWrite v val
  = do
      st <- get
      tell [ IWrite st v val ]


recordAbort :: VM ()
recordAbort = get >>= tell . (:[]) . IAbort

recordCommit :: VM ()
recordCommit = get >>= tell . (:[]) . ICommit


stepThread :: Thread -> Heap -> [Thread] -> VM (Set (Heap, [Thread]))
stepThread (c, sig, r, w) h s
  | finished c = return Set.empty
  | otherwise  = stepI i
    where
      (Just (i,c')) = nextInstr c
      ~(n : sig1) = sig
      ~(m : sig2) = sig1
      
      stepI (Fork c1)
         = sing (h, (c', SVal (Val 0) : sig, r, w) : t : s)
           where t = (c1, [], emptyHeap, emptyHeap)
      stepI (Push n')
         = sing (h, (c', (SVal n') : sig, r, w) : s)
      stepI Add
         = sing (h, (c',  (SVal (n' `op` m')) : sig2, r, w) : s)
           where
             n'  = case n of {SVal v -> v ; _ -> error "impossible ADD" }
             m'  = case m of {SVal v -> v ; _ -> error "impossible ADD" }
      stepI Begin
         = do
            recordBegin
            sing (h, (c', sig, r, w) : s)
      stepI (Mark c1)
         = sing (h, (c', (Han c1) : sig, r,w) : s)
      stepI Unmark
         = case sig of
             (x : Han _ : sig') -> sing (h, (c', x : sig', r, w): s)
             _ -> error "Impossible! VMSemantics.stepI.unmark"
      stepI (Jump off)
         = sing (h, (jump off c', sig, r, w) : s)
      stepI (JumpFalse off)
         = sing (h, (c1, sig1, r, w) : s)
           where
             c1 = if n == (SVal (Val 0)) then jump off c'
                   else c'
      stepI (Read v)
         = do
              s1 <- get
              let
                (n',r',w',b) = case (lookupHeap v w, lookupHeap v r, lookupHeap v h) of
                                   (Just (_,m'), _, _) -> (m', r, w, False)
                                   (Nothing, Just (_,m'), _) -> (m', r,w, False)
                                   (Nothing, Nothing, Just (st, m')) -> (m', insertHeap v st m' r, w, False)
                                   (_, _, _) -> (Val 0, r, insertHeap v s1 (Val 0) w, True)
              recordRead v n'
              when b (recordWrite v (Val 0))
              sing (h, (c', (SVal n') : sig, r', w') : s)
      stepI (Write v)
         = do
             st <- get
             let
               n' = case n of {(SVal x) -> x ; _ -> error "Impossible! SimpleSemantics.stepT.write"}
             recordWrite v n'  
             sing (h, (c', n : sig1, r, insertHeap v st n' w) : s)
      stepI Abort
         = recordAbort >> sing (h, (c1, s1, r, w) : s)
           where
             (c1,s1) = handler sig (skip c')
      stepI Commit
         = if validate r h then
              recordCommit >>
              sing (unionHeap h w, (c', n : sig1, r, w) : s)
           else sing (h, (abort c', sig, r, w) : s)  
             
haltedM :: (Heap, [Thread]) -> Maybe (Heap, Stack)
haltedM (h,s)
  = case traverse haltedT s of
      Just ns -> Just (h,ns)
      Nothing -> Nothing
    where
      haltedT (c, n : [], _, _) = if finished c then Just n else Nothing
      haltedT (_, _, _, _) = Nothing


exec :: (Heap, [Thread]) -> VM (Set (Heap, Stack))
exec = reduceUntil haltedM (uncurry stepVM)

reduceUntil :: (Ord a, Ord b, Monad m)
            => (a -> Maybe b)
            -> (a -> m (Set a))
            -> a
            -> m (Set b)
reduceUntil p reduce inits
  = step (Set.singleton inits, Set.empty)
    where
      step (running, finished')
        = case Set.null running of
              True  ->
                return finished'
              False ->
                do
                  let
                    (rs,fs) = Set.fold partition
                                       (Set.empty, finished')
                                       running
                  rs' <- foldM (\ ac e -> 
                                 do
                                   u  <- reduce e
                                   return (ac `Set.union` u))
                               Set.empty
                               rs
                  step (rs', fs)
                    
      partition e
        = case p e of
            Nothing -> first (Set.insert e)
            Just v  -> second (Set.insert v)
