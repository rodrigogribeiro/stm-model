{-# OPTIONS_GHC -Wall #-}

module STM.Syntax.Syntax where

import STM.Basic.Definitions

-- Syntax for transactions


data Tran = TVal Val
          | TRead Var
          | TWrite Var Tran
          | Tran :+: Tran
          | TIf Tran Tran Tran
          | Tran `TOrElse` Tran
          | TRetry
          deriving (Eq, Ord)

instance Show Tran where
  show (TVal v) = show v
  show (TRead v) = "read " ++ show v
  show (TWrite v t) = "write(" ++ show v ++ ", " ++ show t ++ ")"
  show (TIf t1 t2 t3) = "if " ++ show t1 ++ " then " ++ show t2 ++ " else " ++ show t3
  show (t :+: t') = "(" ++ show t ++ ":+:" ++ show t' ++ ")"
  show (TOrElse t1 t2) = show t1 ++ "||"  ++ show t2
  show TRetry = "retry"

-- Syntax for processes


data Proc = PVal Val
          | PFork Proc
          | PAtomic (Maybe (Stamp, Stamp)) Tran
          | Proc :++: Proc
          deriving (Eq, Ord)  

instance Show Proc where
  show (PVal v) = show v
  show (PFork p) = "fork("++ show p ++ ")"
  show (p :++: p') = "(" ++ show p ++ ":++:" ++ show p' ++ ")"
  show (PAtomic _ t) = "atomic(" ++ show t ++ ")"
  
type Soup = [Proc]
