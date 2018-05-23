\documentclass[14pt]{beamer}
\usepackage[brazil]{babel}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amsfonts,amsthm}
\usepackage{amssymb}
\usepackage{stmaryrd}
\usepackage{latexsym}
\usepackage{hyperref}
\usepackage{graphicx}
\usepackage{xcolor}
\usepackage{proof}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"
%subst numeral a = "\C{" a "}"


\newcommand{\EvalCtxTran}[1]{\ensuremath{\mathbb{T}[#1]}}
\newcommand{\EvalCtxProc}[1]{\ensuremath{\mathbb{P}[#1]}}

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}

\ColourStuff

\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}

%subst comment a = "\orange{\texttt{--" a "}}"

\newcommand{\TStep}[9]{\ensuremath{\langle  #2, #3, #4 \rangle
    \mapsto_{T_{#5}} \langle  #7, #8, #9 \rangle}}
%\usetheme{Luebeck}

%format completions = "\F{completions}"
%format foldr = "\F{foldr}"
%format abortLives = "\F{abortLives}"
%format splits = "\F{splits}"
%format commited = "\F{commited}"
%format otherwise = "\F{otherwise}"
%format some = "\F{some}"
%format prop = "\F{prop}"
%format preservesOrder = "\F{preservesOrder}"
%format legal = "\F{legal}"
%format any = "\F{any}"
%format null = "\F{null}"
%format opacity = "\F{opacity}"
%format History = "\D{History}"
%format all     = "\F{all}"
%format finalStateOpacity = "\F{finalStateOpacity}"
%format inits = "\F{inits}"
%format Bool = "\D{Bool}"
%format TFail = "\C{TFail}"
%format IFail = "\C{IFail}"
%format STM = "\D{STM}"
%format IO = "\D{IO}"
%format TVar = "\D{TVar}"
%format Val  = "\D{Val}"
%format TWrite = "\C{TWrite}"
%format TIf = "\C{TIf}"
%format TOrElse = "\C{TOrElse}"
%format TRetry = "\C{TRetry}"
%format Var = "\D{Var}"
%format Tran = "\D{Tran}"
%format TRead = "\C{TRead}"
%format TAbort = "\C{TAbort}"
%format TVal = "\C{TVal}"
%format Proc = "\D{Proc}"
%format PVal = "\C{PVal}"
%format PFork = "\C{PFork}"
%format PAtomic = "\C{PAtomic}"
%format :++: = "\C{\,\oplus_P\,}"
%format :+: = "\C{\,\oplus_T\,}"
%format Int = "\D{Int}"
%format unVal = "\C{ unVal }"
%format unVar = "\C{ unVar }"
%format orElse = "\F{orElse}"
%format retry = "\F{retry}"
%format Stamp = "\D{Stamp}"
%format unStamp = "\C{ unStamp }"
%format stampOf = "\F{stampOf}"
%format Just = "\C{Just}"
%format Nothing = "\C{Nothing}"
%format Maybe = "\D{Maybe}"
%format Id = "\D{Id}"
%format TIdent = "\D{TIdent}"
%format unId = "\C{unId}"
%format Float = "\D{Float}"
%format transferMoney = "\F{transferMoney}"
%format atomically = "\F{atomically}"
%format writeTVar = "\F{writeTVar}"
%format readTVar = "\F{readTVar}"
%format getR = "\F{getR}"
%format nonBlockGetR = "\F{nonBlockGetR}"
%format Resource = "\D{Resource}"
%format readTVar = "\F{readTVar}"
%format writeTVar = "\F{writeTVar}"
%format atomic = "\F{atomic}"
%format return = "\F{return}"
%format Bool = "\D{Bool}"
%format True = "\C{True}"
%format False = "\C{False}"
%format Item = "\D{Event}"
%format Stamp = "\D{Stamp}"
%format IRead = "\C{IRead}"
%format IWrite = "\C{IWrite}"
%format IBegin = "\C{IBegin}"
%format ICommit = "\C{ICommit}"
%format IAbort = "\C{IAbort}"
%format IRetry = "\C{IRetry}"
%format History = "\D{History}"


\title{An Opaque Model for Software Transactional Memory for Haskell}

\author{Rodrigo Ribeiro \inst{1} \and Andr\'e Du Bois \inst{2}}
\institute{DECOM, Universidade Federal de Ouro Preto (UFOP), Ouro Preto
\and
CDTec, Universidade Federal de Pelotas(UFPel), Pelotas
}

\date{\today}

\begin{document}
     \begin{frame}
         \titlepage
     \end{frame}
     \begin{frame}{Summary}
         \tableofcontents
     \end{frame}
     \section{Brief Bio}
     \begin{frame}{Brief Bio --- (I)}
        \begin{itemize}
           \item MSc in Computer Science (UFMG) - 2007;
           \item DSc in Computer Science (UFMG) - 2013;
           \item Lecturer at Universidade Federal de Ouro Preto.
           \item Post-doc (UFPel) - 2016 - present .
        \end{itemize}
     \end{frame}
     \begin{frame}{Brief Bio --- (II)}
        \begin{itemize}
           \item Main research topic: Type theory.
           \item Applications:
           \begin{itemize}
              \item Programming languages design
              \item Formal verification --- proof assistants.
           \end{itemize}
        \end{itemize}
     \end{frame}
     \begin{frame}{Currently working in... --- (III)}
        \begin{itemize}
           \item Formal semantics for STM.
           \item Formal verification of Featherweight Java typechecker.
           \item Formal semantics and verification of DSLs for temporal media (music, video, etc).
           \item Other projects
           \begin{itemize}
              \item Formal verification of parsing algorithms.
              \item Compilation of partial C programs.
           \end{itemize}
        \end{itemize}
     \end{frame}
     \begin{frame}{This Talk --- (IV)}
        \begin{itemize}
           \item Formal semantics for STM.
           \begin{itemize}
              \item Needed to ensure safety properties of STM.
              \item Results reported in a paper submitted to Haskell Symposium 2017.
              \item We assume that audience is familiar with Haskell syntax and
                    monadic programming. 
           \end{itemize}
        \end{itemize}
     \end{frame}
     \section{Introduction}
     \subsection{Motivation}
     \begin{frame}{Multicores are coming! --- (V)}
        \begin{itemize}
           \item For 50 years, hardware designers delivered 40-50\% increases per year in sequential program performance.
           \item Around 2004, this promise fails because power and cooling issues made impossible to increase clock
                 frequencies.
           \item Result: If we want better performance, parallelism is no longer an option!
        \end{itemize}
     \end{frame}
     \begin{frame}{Parallelism and multicores --- (VI)}
         \begin{itemize}
            \item Parallelism is essential to improve performance on a multi-core machine.
            \item Unfortunately, parallel programming is immensely more error-prone
                  than traditional sequential programming...
            \item How to do it? Locks and conditional variables.
         \end{itemize}
     \end{frame}
     \begin{frame}{Locks and programming --- (VII)}
        \begin{itemize}
           \item \textbf{Correct} use of locks can solve concurrency problems, but...
           \begin{itemize}
              \item Locks are amazingly hard to use correctly!
              \item Incorrect use of locks can cause races and deadlocks which
                    are difficult to debug.
           \end{itemize}
           \item Better solution: Transactions!
        \end{itemize}
     \end{frame}
     \begin{frame}{Transactional Memory --- (VIII)}
        \begin{itemize}
            \item Intuitivelly, write sequential code and wrap it using an \textbf{atomic} block.
            \item Atomic blocks execute in isolation.
            \begin{itemize}
               \item with automatic retry if another conflicting atomic block interferes.
            \end{itemize}
        \end{itemize}
     \end{frame}
     \begin{frame}{How does it work? --- (IX)}
        \begin{itemize}
           \item The TM runtime tries to interleave transactions.
           \item How? Here's one way:
           \begin{itemize}
              \item Read and writes happens in a transaction local log.
              \item At the end, transactions validate its log.
              \item If validation succeeds, changes are committed to memory
              \item If fails, re-runs from the beginning, discarding changes.
           \end{itemize}
        \end{itemize}
     \end{frame}
     \begin{frame}{Our focus: TL2 algorithm --- (X)}
        \begin{itemize}
           \item Uses logs and a global clock.
           \item Every transaction holds its read stamp.
           \begin{itemize}
              \item Global clock value when transaction started.
           \end{itemize}
           \item Every transactional variable has a write stamp.
           \begin{itemize}
              \item When reading, if write stamp > read stamp - abort.
           \end{itemize}
        \end{itemize}
     \end{frame}
     \subsection{Software Transactional Memory in Haskell}
     \begin{frame}{Why Haskell? --- (XI)}
        \begin{itemize}
           \item Haskell is pure functional language, i.e., by default, side-effects
                 are available only throught monads.
           \item This allows for a strict separation between effectful and
                 pure code.
           \item Using monads we can isolate transactional code from other effects
                 present in program.
        \end{itemize}
     \end{frame}
%format fork = "\F{fork}"
%format main = "\F{main}"
%format ThreadId = "\D{ThreadId}"
     \begin{frame}{Concurrency in Haskell --- (XII)}
        \begin{itemize}
           \item Function |fork| spawns a new thread.
           \item It takes an action as its argument.
        \end{itemize}
        \begin{spec}
        fork :: IO a -> IO ThreadId

        main = do {
                 fork someAction ;
                 anotherAction   ;
               ... }
        \end{spec}
     \end{frame}
%format atomic = "\F{atomic}"
%format new = "\F{new}"
%format newTVar = "\F{newTVar}"
    \begin{frame}{Atomic blocks in Haskell --- (XIII)}
        \begin{itemize}
           \item Idea: use a function |atomic| that
                 guarantees atomic execution of its argument
                 computation atomically.
        \end{itemize}
       \begin{spec}
       main = do {
             r <- new 0;
             fork (atomic (someAction));
             atomic (anotherAction); ... }
       \end{spec}
     \end{frame}
     \begin{frame}{STM Haskell interface --- (XIV)}
       \begin{itemize}
          \item Transactional variables:
           \begin{itemize}
               \item |data TVar a = ...|
           \end{itemize}
          \item Transactional memory monad:
            \begin{itemize}
               \item |data STM a = ...|
            \end{itemize}
          \item Creating/ reading / writing variables.
           \begin{spec}
              newTVar :: a -> STM (TVar a)
              readTVar :: TVar a -> STM a
              writeTVar :: TVar a -> a -> STM ()
           \end{spec}
        \end{itemize}
     \end{frame}
     \begin{frame}{STM Haskell interface --- (XV)}
        \begin{itemize}
            \item User controlled abort of transactions.
            \begin{spec}
                retry :: STM a
            \end{spec}
            \item Choice operator.
            \begin{spec}
                orElse :: STM a -> STM a -> STM a
            \end{spec}
            \item Running a transaction.
            \begin{spec}
                atomically :: STM a -> IO a
            \end{spec}
        \end{itemize}
     \end{frame}
     \begin{frame}{STM Haskell example --- (XVI)}
\begin{spec}
type Var = TVar Float

transferMoney :: Float -> Var -> Var -> STM ()
transferMoney amount acc1 acc2
  = do
    v <- readTVar acc1
   if v >= amount
    then do
          writeTVar acc1 (v-amount)
          v2 <- readTVar acc2
          writeTVar acc2 (v2+amount)
    else retry
\end{spec}
     \end{frame}
     \begin{frame}{Transactional memory summary --- (XVII)}
        \begin{itemize}
           \item TM provides a simple programming model to write concurrent code.
           \item STM simplicity (for programmer) has a price:
           \begin{itemize}
              \item Designing efficient algorithms for TM is an art.
              \item Implementations usually use subtle, but efficient, algorithms.
              \item How can we guarantee safety of an TM implementation?
              \item What means ``correctness'' for TM?
           \end{itemize}
        \end{itemize}
     \end{frame}
     \subsection{Transactional Memory Correctness}
     \begin{frame}{Correctness criteria for STM --- (XVIII)}
        \begin{itemize}
           \item Several criteria proposed in literature.
           \item They are based on the concept of TM \textbf{history}.
           \item History:
           \begin{itemize}
              \item Sequence of operations executed during a TM run.
           \end{itemize}
           \item Example:
\[H =\left\bracevert \begin{array}{c}
                 T_1.read\,x \to 0, \\
                 T_1.write(x,1), \\
                 T_2.read(x)\to 1 \\
                 T_1.commit \\
                 T_2.abort\end{array}\right\bracevert\]
        \end{itemize}
     \end{frame}
     \begin{frame}{Correctness criteria for STM --- (XIX)}
        \begin{itemize}
           \item How histories can be used to stabish correctness?
           \item A correct history should be such that:
           \begin{itemize}
              \item Commited transactions should appear to be executed with
                    no other transactions.
              \item Aborted transactions should leave no effect.
              \item Possible to find a history $H'$ s.t. there's
              a \textbf{total order} in which transactions appear to be executed.
           \end{itemize}
        \end{itemize}
     \end{frame}
     \begin{frame}{Correctness criteria for STM --- (XX)}
        \begin{itemize}
           \item How histories can be used to stabish correctness?
           \item A correct history should be such that:
           \begin{itemize}
              \item Possible to find a history $H'$ s.t. there's
              a \textbf{total order} in which transactions appear to be executed.
           \end{itemize}
           \item Here we'll focus on a criteria named \textbf{opacity}.
           \item A TM algorithm is correct if all histories generated by it are
                 opaque.
        \end{itemize}
     \end{frame}
     \section{Formal semantics for transactional memory}
     \begin{frame}{A glimpsy of our proposal --- (XXI)}
        \begin{itemize}
            \item Define a TM algorithm as a small-step operational semantics over a
                  core language.
            \item Semantics should produce the TM history.
            \item Verify that all produced histories satisfy the
                  correctness criteria.
                  \begin{itemize}
                      \item We use property based testing for this.
                  \end{itemize}
        \end{itemize}
     \end{frame}
     \subsection{Core language definition}
     \begin{frame}{Core language --- (XXII)}
         \begin{spec}
-- values
newtype Val = Val { unVal :: Int }
-- variables
newtype Var = Var { unVar :: Int }
-- transaction identifiers
newtype Id = Id { unId :: Int }
-- clock values
newtype Stamp = Stamp { unStamp :: Int } 
         \end{spec} 
     \end{frame}
     \begin{frame}{Core language --- (XXIII)}
\begin{spec}
data Tran =
 TVal Val               -- values
| TRead Var             -- read op.
| TWrite Var Tran       -- write op.
| Tran :+: Tran         -- composition
| TIf Tran Tran Tran    -- conditional
| TOrElse Tran Tran     -- orElse op.
| TRetry                -- user abort
| TAbort                -- runtime abort
\end{spec}
     \end{frame}
     \begin{frame}{Core language --- (XXIV)}
\begin{spec}
-- transaction id + global clock info.
type TIdent = Maybe (Id,Stamp)
data Proc =
 PVal Val                 -- values
| PFork Proc              -- forking
| PAtomic TIdent Tran     -- atomic block
| Proc :++: Proc          -- composition
\end{spec}
     \end{frame}
     \subsection{Definitions and notations used}
     \begin{frame}{Transactional histories --- (XXV)}
\begin{spec}
data Item =
IRead Id Var Val    -- reading a value 
| IWrite Id Var Val -- writing a value
| IBegin Id         -- beginning a transaction.
| ICommit Id        -- commit a transaction.
| IAbort Id         -- runtime abort.
| IRetry Id         -- user abort.

type History = [Item]
\end{spec}
     \end{frame}
     \begin{frame}{Notations: Finite maps --- (XXVI)}
        \begin{itemize}
           \item Empty finite map $\bullet$.
           \item Lookup:
           \[
              h(x) = \left\{\begin{array}{ll}
                               v & \text{if } [x \mapsto v] \in h \\
                               \bot & \text{otherwise}
                            \end{array} \right.
           \]
           \item Right biased union: $h \uplus h'$.
           \item Removing: $h\mid_{x} = h - [x \mapsto v]$, for some $v$.
        \end{itemize}
     \end{frame}
     \begin{frame}{Notations: TM state --- (XXVII)}
        \begin{itemize}
           \item Heaps, read and write sets represented as finite maps.
           \item $\Theta=\langle \Theta_h, \Theta_r, \Theta_w, \Theta_T \rangle$, where:
           \begin{itemize}
              \item $\Theta_h$ : heap
              \item $\Theta_r$ and $\Theta_w$: finite maps between trans. id and its read / write sets.
              \item $\Theta_T$: finite map between trans. id and the transaction itself.
           \end{itemize}
        \end{itemize}
     \end{frame}
     \section{TL2 semantics}
     \begin{frame}{Reading a variable: intuition --- (XXVIII)}
        \begin{itemize}
           \item $\Theta(x,i,j)$: reads the value of variable $x$ in transaction $j$ which has
            read stamp $i$.
           \item How reading proceeds:
           \begin{itemize}
              \item If $x$ is in $j$ write set, return its value.
              \item If $x$ is in $j$ read set and $i$ isn't less than $x$
                      write stamp, return $x$ associated value.
              \item Lookup value in heap. If $x$ value has a stamp greather than $i$, abort.
              \item Otherwise, update read-set.
           \end{itemize}
        \end{itemize}
     \end{frame}
     \begin{frame}{Reading a variable, formally --- (XXIX)}
\begingroup
\everymath{\scriptstyle}
\large
  \[
  \Theta(x,i,j) = \left\{
  \begin{array}{ll}
     (v,\Theta) & \textit{if }\:\Theta_w(x,j) = (i',v)\\
     (v,\Theta) & \textit{if }\:\Theta_w(x,j) = \bot,\\
                & \:\:\:\:\:\Theta_r(x,j) = (i',v), i \geq i' \\
     (v, \Theta_r\,[j,x \mapsto v]) & 
        \textit{if }\:\Theta_w(x) = \Theta_r(x) = \bot,\\
                                       & \:\:\:\:\:  \Theta_h(x) = (i',v),
                                     \textit{ and } i \geq i' \\
                           |TAbort| & \textit{if }\: \Theta_h(x) = (i',v)
                                    \textit{ and } i < i'
  \end{array}
                                  \right.
  \]        

\endgroup
     \end{frame}
     \begin{frame}{Consistency check --- (XXX)}
        \begin{itemize}
           \item $consistent(\Theta,i,j)$ holds if transaction $j$ has finished its execution
                 on a valid view of memory.
        \end{itemize}
  \[
     \begin{array}{lcl}
\\
        consistent(\Theta,i,j) & = & \forall x. \Theta_r(x,j) = (i,v) \to \\
      & & \Theta_h(x) = (i',v) \land i \geq i'
     \end{array}
  \]
     \end{frame}
     \begin{frame}{Semantics --- (XXXI)}
        \begin{itemize}
          \item Transaction semantics uses triples $\langle \Theta, \sigma, t \rangle$:
          \begin{itemize}
             \item $\Theta$: heap and TM logs.
             \item $\sigma$: TM execution history
             \item $t$: transaction being executed.
             \item $i$: current read stamp
             \item $j$: current transation id.
          \end{itemize}
          \[\langle \Theta,\,\sigma,\,t \rangle \mapsto_{T_{i\,j}}
          \langle \Theta',\,\sigma',\, t'\rangle\]
        \end{itemize}
     \end{frame}
     \begin{frame}{Semantics --- (XXXII)}
        \begin{itemize}
           \item Process semantics uses 5-uples
           \begin{itemize}
             \item $\Theta$: heap and TM logs.
             \item $\sigma$: TM execution history
             \item $i$: global clock
             \item $j$: last transaction id used.
             \item $p$: process being executed.
           \end{itemize}
          \[\langle \Theta,\,\sigma,\,j,\,i,\,t \rangle \mapsto_{P}
          \langle \Theta',\,\sigma',\,j',\,i',\, t'\rangle\]
        \end{itemize}
     \end{frame}
     \begin{frame}{Evaluation Contexts --- (XXXIII)}
        \[
          \begin{array}{cc}
          \begin{array}{rcl}
                      \EvalCtxTran{\cdot} & ::=    & |TWrite|\, v\:\EvalCtxTran{\cdot}\\
                                                   & \mid &\EvalCtxTran{\cdot}\: |:+:| t\\
                                                   & \mid & |TVal|\,v |:+:| \EvalCtxTran{\cdot}\\
                                                   & \mid & |TIf|\:\EvalCtxTran{\cdot}\:t\:t' \\
                                                   & \mid & |TOrElse|\:\EvalCtxTran{\cdot}\:t\\

          \end{array} &
          \begin{array}{rcl}
                      \EvalCtxProc{\cdot} & ::=    & |PFork|\:\EvalCtxProc{\cdot}\\
                                                   & \mid &\EvalCtxProc{\cdot}\:|:++:| t\\
                                                   & \mid & |PVal|\,v\,|:++:|\EvalCtxProc{\cdot}\\
                                                   & \mid & |PAtomic|\:\EvalCtxProc{\cdot}

          \end{array}
          \end{array}
        \]
     \end{frame}
     \begin{frame}{Evaluation context reduction --- (XXXIV)}
\[
\begin{array}{c}
  \infer[_{(TContext)}]
        { \langle \Theta,\,\sigma,\,\EvalCtxTran{t}\rangle \mapsto_{T_{i\,j}}
          \langle \Theta',\,\sigma',\,\EvalCtxTran{t'}\rangle }
        { \langle \Theta,\,\sigma,\,t \rangle \mapsto_{T_{i\,j}}
          \langle \Theta',\,\sigma',\, t'\rangle } \\ \\ \\
  \infer[_{(PContext)}]
        { \langle \Theta,\,\sigma,\,j,\,i,\EvalCtxProc{p} : s\rangle \mapsto_{P}
          \langle \Theta,\,\sigma',\,j',\,i',\,\EvalCtxProc{p'} : s\rangle }
        { \langle \Theta,\,\sigma,\,j,\,i,\,t \rangle \mapsto_{P}
          \langle \Theta',\,\sigma',\,j',\,i',\, t'\rangle }
\end{array}
\]        
     \end{frame}
     \begin{frame}{Read Semantics --- (XXXV)}
\[
\begin{array}{c}
  \infer[_{(TReadOk)}]
        { \langle \Theta,\, \sigma, |TRead|\,v \rangle \mapsto_{T_{i\,j}}
          \langle \Theta',\, \sigma',\,|TVal|\,val\rangle }
        {\Theta(v,i,j) = (val,\Theta') & \sigma' = |IRead|\,j\,v\,val\,:\sigma}
  \\
  \\
  \\
  \infer[_{(TReadFail)}]
        { \langle \Theta,\, \sigma, |TRead|\,v \rangle \mapsto_{T_{i\,j}}
          \langle \Theta, \, \sigma',\, |TAbort| \rangle}
        {\Theta(v,i,j) = (|TAbort|,\Theta') & \sigma' = |IAbort|\,j\,:\sigma} 
\end{array}
\]
     \end{frame}
     \begin{frame}{Write Semantics --- (XXXVI)}
\[
\begin{array}{c}
  \infer[_{(TWriteVal)}]
        { \langle \Theta, \, \sigma, |TWrite|\,v\,t\rangle \mapsto_{T_{i\,j}}
          \langle \Theta', \, \sigma',\,t\rangle}
        {\begin{array}{c}
            t = |TVal|\,val \\
            \sigma' = |IWrite|\,j\,v\,val\, : \sigma \\
            \Theta' = \langle \Theta_h, \Theta_r, \Theta_w[j,x \mapsto val], \Theta_T\rangle
         \end{array}}
  \\ \\ \\
  \infer[_{(TWriteFail)}]
        { \langle \Theta, \,\sigma, |TWrite|\,v\,|TFail|\rangle \mapsto_{T_{i\,j}}
          \langle \Theta, \, \sigma,\, |TFail| \rangle }
        { }
\end{array}
\]
     \end{frame}
     \begin{frame}{Composition Semantics --- (XXXVII)}
\begingroup
\everymath{\scriptstyle}
\large
\[
\begin{array}{c}
  \infer[_{(TAddVal)}]
        { \langle \Theta, \, \sigma,\, (|TVal|\,val_1) |:+:| (|TVal|\,val_2) \rangle \mapsto_{T_{i\,j}}
          \langle \Theta, \, \sigma,\, |TVal|\,val \rangle}
        {val = val_1 + val_2}
  \\ \\
  \infer[_{(TAddL)}]
        { \langle \Theta,\,\sigma,\,|TFail|\,|:+:| t\rangle \mapsto_{T_{i\,j}}
          \langle \Theta',\,\sigma', |TFail|\rangle}
        { }

%\langle \Theta,\,\sigma,\,t\rangle \mapsto_{T_{i\,j}}
%         \langle \Theta',\,\sigma',\,|TFail|\rangle 

  \\ \\
  \infer[_{(TAddR)}]
        { \langle \Theta,\,\sigma,\, (|TVal|\, val) |:+:| |TFail| \rangle \mapsto_{T_{i\,j}}
          \langle \Theta',\,\sigma',\,|TFail| \rangle }
        { }
\end{array}
\]
\endgroup
     \end{frame}
     \begin{frame}{Conditional Semantics --- (XXXVIII)}
\[
  \begin{array}{c}
     \infer[_{(TIfZero)}]
           {\langle \Theta,\sigma,|TIf|\,(|TVal 0|)\,t\,t'\rangle \mapsto_{T_{i\,j}}
            \langle \Theta,\sigma,\,t\rangle}
           {}
     \\ \\ \\
     \infer[_{(TIfNonZero)}]
           {\langle \Theta,\sigma,|TIf|\,(|TVal v|)\,t\,t'\rangle \mapsto_{T_{i\,j}}
            \langle \Theta,\sigma,\,t'\rangle}
           {v \neq 0}    \\ \\ \\
     \infer[_{(TIfFail)}]
           { \langle \Theta,\,\sigma,\,|TIf|\,|TFail|\,t\,t'\rangle\mapsto_{T_{i\,j}}
             \langle \Theta,\,\sigma,\,|TFail|\rangle }
           {}

  \end{array}
\]
     \end{frame}
     \begin{frame}{OrElse Semantics --- (XXXIX)}
\begingroup
\everymath{\scriptstyle}
\large
\[
  \begin{array}{c}
     \infer[_{(TOrElseVal)}]
           { \langle \Theta,\,\sigma,\,|TOrElse|\,(|TVal|\:v)\,t'\rangle \mapsto_{T_{i\,j}}
             \langle \Theta',\,\sigma',\,|TVal|\,v \rangle }
           {  }
     \\ \\
     \infer[_{(TOrElseR)}]
           { \langle \Theta,\,\sigma,\,|TOrElse|\,|TRetry|\,t'\rangle \mapsto_{T_{i\,j}}
             \langle \Theta,\,\sigma,\,t' \rangle }
           { }
      \\ \\
     \infer[_{(TOrElseA)}]
           { \langle \Theta,\,\sigma,\,|TOrElse|\,|TAbort|\,t'\rangle \mapsto_{T_{i\,j}}
             \langle \Theta,\,\sigma,\,|TAbort| \rangle }
           {  }
  \end{array}
\]
\endgroup
     \end{frame}
     \begin{frame}{Process preemption --- (XL)}
\[
   \infer[_{(PPreempt)}]
         { \langle \Theta,\,\sigma,\,j,\,i,\,p : s\rangle \mapsto_{P}
           \langle \Theta',\,\sigma',\,j',\,i',p : s'\rangle }
         { \langle \Theta,\,\sigma,\,j,\,i,\,s\rangle \mapsto_{P}
           \langle \Theta',\,\sigma',\,j',\,i',\,s'\rangle } 
\]

     \end{frame}
     \begin{frame}{Forking semantics --- (XLI)}
\[
    \infer[_{(PFork)}]
          {\langle \Theta,\,\sigma,\,j,\,i,\, (|PFork|\,p) : s \rangle \mapsto_{P}
           \langle \Theta,\,\,\sigma,\,j,\,i,\, s' \rangle}
          {s' = |PVal|\,0 : p : s}
\]
     \end{frame}
     \begin{frame}{Atomic block semantics --- (XLII)}
\begingroup
\everymath{\scriptstyle}
\Large
\[
  \begin{array}{c}
  \infer[_{(PAt1)}]
        {\langle \Theta,\,\sigma,\,j,\,i,\,|PAtomic|\,|()|\,t : s\rangle\mapsto_{P}
         \langle \Theta',\,\sigma',\,j + 1,\,i,\, s'\rangle}
        {\begin{array}{c}
         \sigma' = |IBegin|\,j : \sigma\\
         s' = s |++| [|PAtomic|\,(i,j)\,t] \\
         \Theta_1 = \langle \Theta_h, \Theta_r\,[j\mapsto \bullet], \Theta_w\,[j\mapsto \bullet], \Theta_T\,[j\mapsto t]\rangle
         \end{array}}
  \end{array}      
\]
\endgroup
     \end{frame}
     \begin{frame}{Atomic block semantics --- (XLIII)}
\begingroup
\everymath{\scriptstyle}
\large
\[
  \begin{array}{c}
     \infer[_{(PAt2)}]
           {\langle \Theta,\,\sigma,\,j,\,i,\,|PAtomic|\,v : s \rangle \mapsto_{P}
            \langle \Theta',\,\sigma',\,j,\,i + 1,\,|PVal|\,n : s \rangle}
           {\begin{array}{cc}
              v = |TVal|\, n         & consistent(\Theta,i,j) \\
              \sigma' = |ICommit|\,j : \sigma & 
              \Theta' = \langle \Theta_h',\,\Theta_r\mid_j,\,\Theta_w\mid_j \rangle \\
              \multicolumn{2}{c}{\Theta_h'  = \Theta_h \uplus \Theta_w(j)} \\
            \end{array}}
  \end{array}
\]
\endgroup
     \end{frame}
     \begin{frame}{Atomic block semantics --- (XLIV)}
\begingroup
\everymath{\scriptstyle}
\Large
\[
  \begin{array}{c}
     \infer[_{(PAt3)}]
           {\langle \Theta,\,\sigma,\,j,\,i,\,|PAtomic|\,|TFail| : s \rangle \mapsto_{P}
            \langle \Theta',\,\sigma,\,j + 1,\,i,\,s' \rangle}
           {\begin{array}{c}
              \Theta' = \langle\Theta_h,\Theta_r\mid_j,\Theta_w\mid_j,\Theta_T\mid_j\rangle\\
              s' = s |++| |PAtomic|\,()\,t\,\,\,\,\,\,\,t = \Theta_t(j)
            \end{array}}
  \end{array}
\]
\endgroup
     \end{frame}
\section{Checking Opacity}
\begin{frame}{Checking Opacity --- (XLV)}
   \begin{itemize}
      \item We check safety properties using Quickcheck, a Haskell library for
            property based testing.
      \item Library formed by combinators for building generators and properties.
      \begin{itemize}
         \item Generators build random values which are checked against relevant properties.
         \item Combinators for properties mimics first-order logic conectives and quantifiers.
      \end{itemize}
   \end{itemize}
\end{frame}
\begin{frame}{Defining Opacity --- (XLVI)}
  \begin{itemize}
     \item A TM algorithm is opaque if all prefixes of its generated histories are final state opaque.
     \item In Haskell:
  \end{itemize}
\begin{spec}
opacity :: History -> Bool
opacity = all finalStateOpacity . inits
\end{spec}
\end{frame}
\begin{frame}{Defining Opacity --- (XLVII)}
  \begin{itemize}
     \item A history is final state opaque if exists some completion of
           it that preserves real time order and all of its transactions are legal.
     \item In Haskell:
  \end{itemize}
\begin{spec}
finalStateOpacity :: History -> Bool
finalStateOpacity
  = some prop . completions
    where
      prop tr = preservesOrder tr && legal tr
      some p xs = (null xs) || (any p xs)
\end{spec}
\end{frame}
\begin{frame}{Defining Opacity --- (XLVIII)}
   \begin{itemize}
      \item Completion of a history $H$ is a history $S$, s.t.
      \begin{itemize}
         \item All live and non-commit pending transactions of $H$ are aborted in $S$; and
         \item All commit pending transactions of $H$ are aborted or committed in $S$.
      \end{itemize}
      \item Our model we do not consider commit-pending transactions.
      \item Complete a history is just abort all live transactions.
   \end{itemize}
\end{frame}
\begin{frame}{Defining Opacity --- (XLIX)}
   \begin{itemize}
      \item Real time order: $t_k \prec_H t_m$
      \begin{itemize}
         \item $t_k$ is completed and its last event occurs before $t_m$s first.
      \end{itemize}
      \item A history $H'$ preserves the real time ordering of $H$:
      \[
          \forall t_k\,t_m. t_k \prec_H t_m \to t_k \prec_{H'} t_m
      \]
   \end{itemize}
\end{frame}
\begin{frame}{Defining Opacity --- (L)}
   \begin{itemize}
      \item Legal histories.
      \begin{itemize}
         \item A history is said to be \emph{legal}
               if all values read after a write in a variable
               are equal to last value written
      \end{itemize}
   \end{itemize}
\end{frame}
\begin{frame}{Checking Opacity --- (LI)}
   \begin{itemize}
      \item We use function |opacity| as a Quickcheck property over
            histories produced by executing random generated programs.
      \item Semantics passes in all test-suit runs.
   \end{itemize}
\end{frame}
\begin{frame}{Checking Opacity --- (LII)}
   \begin{itemize}
      \item So, our semantics does enjoy opacity?
      \begin{itemize}
         \item As pointed by Djikstra: ``Tests can only prove the presence of bugs...''.
      \end{itemize}
      \item In order to afirm this categorically, we need a formal proof.
      \begin{itemize}      
         \item A venue that we intend to pursue in future work.
      \end{itemize}
   \end{itemize}
\end{frame}
\section{Conclusions}
\begin{frame}{History not told... (LIII)}
   \begin{itemize}
      \item Alternative STM-Haskell based semantics (does not have opacity).
      \item Compilation to virtual machine.
      \item Another correctness criteria: markability.
      \item Other properties verified
      \begin{itemize}
         \item Compilation preserves safety properties.
         \item Equivalence of safety properties.
      \end{itemize}
   \end{itemize}
\end{frame}
\begin{frame}{Conclusions --- (LIV)}
   \begin{itemize}
      \item We define small-step operational semantics for STM-Haskell like language.
      \begin{itemize}
         \item TL2-based semantics.
         \item STM-Haskell based semantics.
      \end{itemize}
      \item Implemented interpreters for the semantics and relevant properties over it using Haskell.
   \end{itemize}
\end{frame}
\begin{frame}{Conclusions --- (LV)}
   \begin{itemize}
      \item Property based testing.
      \begin{itemize}
         \item Allows for quickly identify errors in semantics --- counter-examples.
         \item Provides some degree of assurance, before using more formal approachs.
      \end{itemize}
   \end{itemize}
\end{frame}
\end{document}
