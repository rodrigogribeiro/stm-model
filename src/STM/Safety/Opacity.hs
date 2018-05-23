{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TupleSections #-}

module STM.Safety.Opacity where

import Data.List
import qualified Data.Map as Map
import Data.Maybe

import STM.Basic.Definitions
import STM.Safety.Basics


-- opacity: all finite prefixes of a trace are
-- final state opaque

opacity :: Trace -> Bool
opacity = all finalStateOpacity . inits

-- final state opacity
-- A trace is final state opaque if some of its completion:
-- 1) it preserves real time order and;
-- 2) it is legal 

finalStateOpacity :: Trace -> Bool
finalStateOpacity
  = any' prop . completions
    where
      prop tr = preservesOrder tr && legal tr
      any' p xs = (null xs) || (any p xs)
      

legal :: Trace -> Bool
legal
  = all isLegal . sequentialSpecs
    where
      isLegal = fst . foldr step (True,Map.empty) . reverse
      step (IRead _ v val) (c,m)              -- value record should be
         = maybe (val == (Val 0), m)          -- equal to last value written
                 ((,m) . (c &&) . (== val))
                 (Map.lookup v m)
      step (IWrite _ v val) (c,m)
        = (c,Map.insert v val m)
      step _ ac = ac

          
-- group traces by variable, forming its sequential specification

sequentialSpecs :: Trace -> [Trace]
sequentialSpecs 
  = Map.elems . (foldr step Map.empty) . mapMaybe readOrWrite
    where
      step (v,i) ac
         = maybe (Map.insert v [i] ac)
                 (\is -> Map.insert v (i:is) ac)
                 (Map.lookup v ac)
