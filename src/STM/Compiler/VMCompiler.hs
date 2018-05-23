module STM.Compiler.VMCompiler where

import STM.Basic.Definitions
import STM.Syntax.Syntax
import STM.VM.Instruction


compileTran :: Tran -> [Instr]
compileTran (TVal i)
  = [ Push i ]
compileTran (x :+: y)
  = compileTran x ++ compileTran y ++ [ Add ]
compileTran (TRead v)
  = [ Read v ]
compileTran (TWrite v t)
  = compileTran t ++ [ Write v ]
compileTran TRetry
  = [ Abort ]
compileTran (t `TOrElse` t')
  = [ Mark (Code [] (compileTran t')) ] ++
    compileTran t ++
    [ Unmark ]
compileTran (TIf t t' t'')
  = compileTran t ++
    [ JumpFalse off1 ] ++
    c1 ++ [ Jump off2 ] ++ c2
   where
     c1 = compileTran t'
     off1 = length c1 + 1
     c2 = compileTran t''
     off2 = length c2
  

compileProc' :: Proc -> [Instr]
compileProc' (PVal v)
  = [ Push v ]
compileProc' (x :++: y)
  = compileProc' x ++
    compileProc' y ++ [ Add ]
compileProc' (PAtomic _ t)
  = Begin : (compileTran t) ++ [ Commit ]
compileProc' (PFork p)
  = [ Fork (compileProc p) ]

compileProc :: Proc -> Code
compileProc = Code [] . compileProc'

