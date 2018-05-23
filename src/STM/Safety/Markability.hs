module STM.Safety.Markability where

import qualified Data.Map as Map

import STM.Basic.Definitions
import STM.Syntax.Syntax
import STM.Safety.Basics

-- markability definition
-- the marking of a history is the conjunction of 3 properties
--- 1: write observation
--- 2: read preservation 
--- 3: real time order preservation


markability :: Trace -> Bool
markability h = and [ writeObservation h''
                    , readPreservation h'
                    , preservesOrder h' ]
                where
                  h' = concat $ completions h
                  h'' = filter valid h'
                  valid (IRead _ _ _) = True
                  valid (IWrite _ _ _) = True
                  valid _ = False


-- write observation means that each read operation should read
-- the most current value.

writeObservation :: Trace -> Bool
writeObservation h
  = Map.foldr ((&&) . snd) True m
    where
     m = foldr step Map.empty h
     step (IRead _ v val) m
       = case Map.lookup v m of
            Nothing   -> Map.insert v ((Val 0),True) m
            Just (val',ac) -> Map.insert v (val, ac && val == val') m
     step (IWrite _ v val) m
       = Map.insert v (val, True) m
     step _ ac = ac
     
-- read preservation means that the read value is not overwritten
-- between the point where the value is read and the point where
-- commit of transaction happens

readPreservation :: Trace -> Bool
readPreservation h
  = all (fst . foldr step (True, Map.empty)) h'
    where
      step (IRead i v val) (ac,m)
        = case Map.lookup v m of
             Nothing   -> (ac , Map.insert v  (i,(Val 0)) m)
             Just (i',val') -> (ac && (val == val' || i == i') , m)
      step (IWrite i v val) (ac,m)
        = case Map.lookup v m of
             Nothing   -> (ac , Map.insert v (i,val) m)
             _         -> (ac , m)
      step _ ac = ac       
      -- first get committed transactions
      h' = [ l | l <- splits h
               , isCommit (last l) ]
      isCommit (ICommit _) = True
      isCommit _ = False
