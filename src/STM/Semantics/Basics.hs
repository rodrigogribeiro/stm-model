module STM.Semantics.Basics where

import Control.Arrow

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Either
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import STM.Basic.Definitions
import STM.Syntax.Syntax


-- monad for transaction execution and its related operations

type STM a = ReaderT (Stamp, Heap)
                     (WriterT Trace
                              (StateT (WriteSet, ReadSet)
                                      Identity)) a

  
runSTM :: Stamp -> Heap -> Tran -> (Tran -> STM (Set (Either Tran Val))) ->
                             ( ( Set (Either Tran Val)
                                     , [Item])
                                   , (WriteSet, ReadSet))
runSTM tid h t step
  = runIdentity (runStateT
                    (runWriterT
                         (runReaderT (step t)
                                     (tid, h)))
                    (emptyHeap, emptyHeap))


-- register read

recordRead :: Stamp -> Var -> Val -> STM (Set Tran)
recordRead st v val
  = do
      tell [ IRead st v val ]
      singleton (TVal val)

-- register write

recordWrite :: Stamp -> Var -> Val -> STM (Set Tran)
recordWrite st v val
  = do
      tell [ IWrite st v val ]
      singleton (TVal val)

recordAbort :: Stamp -> STM (Set Tran)
recordAbort i
  = do
      tell [ IAbort i ]
      empty

registerCommit :: Stamp -> ProcM ()
registerCommit i
  = writeTrace [ ICommit i ]

registerBegin :: Stamp -> ProcM ()
registerBegin i
  = writeTrace [ IBegin i ]

-- read and write set operations

updateReadSet :: Var -> (Stamp, Val) -> STM ()
updateReadSet v (st,val)
  = modify (second (insertHeap v st val))
  
updateWriteSet :: Var -> (Stamp, Val) -> STM ()
updateWriteSet v (st,val)
  = modify (first (insertHeap v st val))

writeSet :: STM WriteSet
writeSet = gets fst

readSet :: STM ReadSet
readSet = gets snd

-- monad for process execution

type Tid = Int

data PState
  = PState {
      transid :: Tid   -- transaction id
    , clock   :: Stamp -- commit counter
    , ptrace  :: Trace -- trace
    }

type ProcM a = (StateT PState Identity) a

freshTid :: ProcM Stamp
freshTid
  = do
      i <- gets transid
      modify (\p -> p{ transid = transid p + 1})
      registerBegin (Stamp i)
      return (Stamp i)

writeTrace :: [Item] -> ProcM ()
writeTrace tr
  = modify (\p -> p{ ptrace = ptrace p ++ tr})

-- generic operations over monads

empty :: Monad m => m (Set a)
empty = return Set.empty

singleton :: Monad m => a -> m (Set a)
singleton = return . Set.singleton

appM :: ( Monad m
        , Ord b) => (a -> b) -> m (Set a) -> m (Set b)
f `appM` m
  = (f `Set.map`) <$> m

-- generic transitive closure operation
  
reduceUntil :: (Ord a, Ord b, Monad m)
            => (a -> Maybe b)
            -> (a -> m (Set a))
            -> a
            -> m (Set b)
reduceUntil p reduce inits
  = step (Set.singleton inits, Set.empty)
    where
      step (running, finished)
        = case Set.null running of
              True  ->
                return finished
              False ->
                do
                  let
                    (rs,fs) = Set.fold partition
                                       (Set.empty, finished)
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

-- type for reading functions

type ReadValue = Var -> Stamp -> STM (Set Tran)

-- type for commit validation

type IsValidCommit = ReadSet -> Heap -> Bool

-- generic instantiation of semantics

readVar :: ReadValue -> Var -> STM (Set Tran)
readVar rd v
  = tranId >>= rd v

-- write operation

writeVar :: Var -> Val -> STM (Set Tran)
writeVar v val
  = do
      i <- tranId
      updateWriteSet v (i,val)
      recordWrite i v val

-- aborting a transaction
retry :: STM (Set Tran)
retry
  = do
      i <- tranId
      recordAbort i

-- single step for transactions

stepTran :: ReadValue -> Tran -> STM (Set Tran)
stepTran _ (TVal _)
  = empty
stepTran rd (TRead v)
  = readVar rd v
stepTran _ (TWrite v (TVal val))
  = writeVar v val
stepTran rd (TWrite v t)
  = (TWrite v) `appM` stepTran rd t
stepTran _ ((TVal val) :+: (TVal val'))
  = singleton (TVal (val `op` val'))
stepTran rd (TVal val :+: t')
  = (TVal val :+:) `appM` stepTran rd t'
stepTran rd (t :+: t')
  = (:+: t') `appM` stepTran rd t
stepTran rd (TIf (TVal val) t' t'')
  | val == Val 0 = stepTran rd t'
  | otherwise    = stepTran rd t''
stepTran rd (TIf t t' t'')
  = (\ t1 -> TIf t1 t' t'') `appM` stepTran rd t
stepTran _ (t@(TVal _) `TOrElse` _)
  = singleton t
stepTran rd (TRetry `TOrElse` t')
  = stepTran rd t'
stepTran rd (t `TOrElse` t')
  = (flip TOrElse t') `appM` stepTran rd t
stepTran _ TRetry
  = retry

-- top level function for small step semantics for transactions

smallStepTran :: ReadValue -> Tran -> STM (Set (Either Tran Val))
smallStepTran rd = reduceUntil isValT (stepTran rd)


-- determining when a transaction is a value.

isValT :: Tran -> Maybe (Either Tran Val)
isValT (TVal val)
  = Just (Right val)
isValT TRetry
  = Just (Left TRetry)
isValT _
  = Nothing

-- one step in process semantics

stepSoup :: IsValidCommit -> ReadValue -> (Heap, Soup) -> ProcM (Set (Heap, Soup))
stepSoup _ _ (_, [])
  = empty
stepSoup c rd (h, (p : ps))
  = do
      ps1 <- (second (p :)) `appM` stepSoup c rd (h, ps)
      ps2 <- stepProc c rd p h ps
      return (ps1 `Set.union` ps2)

stepProc :: IsValidCommit -> ReadValue -> Proc -> Heap -> Soup -> ProcM (Set (Heap, Soup))
stepProc _ _ (PVal _) _ _
  = empty
stepProc _ _ (PFork p) h s
  = singleton (h, v0 : p : s)
    where v0 = PVal (Val 0)
stepProc _ _ (PAtomic Nothing t) h s
  = do
      i <- freshTid
      j <- gets clock
      singleton (h, (s ++ [PAtomic (Just (j,i)) t]))
stepProc c rd (PAtomic (Just (j,i)) t) h s
  = do
      let
        ((res, tr),(ws,rs))
          = runSTM i h t (smallStepTran rd)
      writeTrace tr
      case isValT res of
        Just (Left TRetry) -> undefined
        Just (Right v)     -> undefined
        Nothing            -> undefined
{-stepProc c rd (PAtomic _ t) h s
  = do
      tid <- freshTid
      let
        ((res, tr),(ws, rs))
          = runSTM tid h t (smallStepTran rd)
      writeTrace tr
      case Set.null (Set.filter isLeft res) of
        True ->
          do
            h' <- commitTran c tid h rs ws
            let h'' = if isJust h' then fromJust h' else h
                step ac (Right v)
                  = Set.insert (h'', PVal v : s) ac
                step ac  _
                  = ac
            return (Set.foldl step Set.empty res)
        False -> singleton (h, PVal (Val 0) : s) -}
stepProc _ _ ((PVal v) :++: (PVal v')) h s
  = singleton (h, (PVal (v `op` v')) : s)
stepProc c rd ((PVal v) :++: p') h s
  = (second ((PVal v) : )) `appM` stepSoup c rd (h, (p' : s))
stepProc c rd (p :++: p') h s
  = (second (mapHead (:++: p'))) `appM` stepSoup c rd (h, (p : s))

isValSoup :: (Heap, Soup) -> Maybe (Heap, [Val])
isValSoup (h,s)
  = case traverse isValProc s of
       Nothing -> Nothing
       Just vs -> Just (h,vs)
    where
      isValProc :: Proc -> Maybe Val
      isValProc (PVal v)
        = Just v
      isValProc _
        = Nothing

smallStepSoup :: IsValidCommit -> ReadValue -> (Heap, Soup) -> ProcM (Set (Heap, [Val]))
smallStepSoup c rd = reduceUntil isValSoup (stepSoup c rd)

runSoup :: IsValidCommit -> ReadValue -> Soup -> (Set (Heap, [Val]), PState)
runSoup c rd s
  = runIdentity (runStateT (smallStepSoup c rd (emptyHeap, s)) initialPState)
    where
      initialPState :: PState
      initialPState = undefined

exec :: IsValidCommit -> ReadValue -> Soup -> Trace
exec c rd = ptrace . snd . (runSoup c rd)

-- commiting a transaction

commitTran :: IsValidCommit -> Stamp -> Heap -> ReadSet -> WriteSet -> ProcM (Maybe Heap)
commitTran validate tid h rs ws
  = case validate rs h of
       True  ->
         do
           registerCommit tid
           return (Just (h `unionHeap` ws))
       False -> return Nothing 


-- utility code

mapHead :: (a -> a) -> [a] -> [a]
mapHead _ [] = []
mapHead f (x:xs) = f x : xs
  
