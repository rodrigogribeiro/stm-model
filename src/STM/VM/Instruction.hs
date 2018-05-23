{-# OPTIONS_GHC -Wall #-}

module STM.VM.Instruction where

import STM.Basic.Definitions

-- VM instructions

data Instr
  = Push Val
  | Add
  | Read Var
  | Write Var
  | Begin 
  | Commit 
  | Fork Code
  | Jump Offset
  | JumpFalse Offset
  | Abort 
  | Mark Code
  | Unmark   
  deriving (Eq, Ord, Show)


-- VM code interface

type Offset = Int

data Code
      = Code {
          executed :: [Instr]   -- previously executed instructions, in reverse order.
        , nexts    :: [Instr]   -- next instructions.           
        } deriving (Eq, Ord, Show)

-- next instruction: Nothing, if no more instructions to be executed

nextInstr :: Code -> Maybe (Instr, Code)
nextInstr (Code _ []) = Nothing
nextInstr (Code ex (i:nx)) = Just (i, Code (i : ex) nx)

-- true if code finished

finished :: Code -> Bool
finished = null . nexts

-- abort semantics

abort :: Code -> Code
abort c@(Code [] _) = c
abort (Code (i:ex) nx)
  | isBegin i = Code ex (i : nx)
  | otherwise = abort (Code ex (i : nx))
    where
      isBegin Begin  = True
      isBegin _      = False

-- jump instructions semantics

jump :: Offset -> Code -> Code
jump off (Code os is)
     | off < 0 = Code os2 (os1 ++ is)
     | otherwise = Code (is1 ++ os) is2
     where
       off' = abs off
       (is1,is2) = splitAt off' is
       (os1,os2) = splitAt off' os  


