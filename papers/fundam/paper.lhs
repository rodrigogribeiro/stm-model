\documentclass{fundam}

\usepackage{booktabs} % For formal tables
\usepackage{hyperref}
\usepackage{graphicx}
\usepackage{float}
\usepackage{proof}
\usepackage{amssymb}


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
\newcommand{\yellowBG}[1]{\colorbox[rgb]\subsection{Markability}

Another criteria for TM safety is markability~\cite{LesaniP14}, which decomposes opacity in a conjunction of
three invariants, namely: 1) write-observation, which requires that each read operation returns the most current value;
2) read-preservation requires that the read location is not overwritten in the interval that the location is read and
the transaction takes effect and 3) real-time preservation property, already present in opacity. Also,
Lesani et. al.~\cite{LesaniP14} proves that markability is equivalent to opacity.

A history is said to be \emph{final state markable} if there is an extension of it that is write-observant, read-preserving
and preserves real-time. An extension of a history is obtained by committing or aborting its commit-pending transactions
and aborting the other live transactions. Our Haskell implementation of markability is just the conjunction of these
previous properties and uses function |completions| that generates a list of events grouped by transaction.

%format markability = "\F{markability}"
%format concat = "\F{concat}"
%format writeObservation = "\F{writeObservation}"
%format readPreservation = "\F{readPreservation}"

\begin{spec}
markability :: History -> Bool
markability h
    = and [ writeObservation h'
          , readPreservation h'
          , preservesOrder h' ]
                where
                  h' = concat $ completions h
\end{spec}

Function |writeObservation| checks if a history is write-observant. It builds a mapping between variables
and last values written and traverses the history verifying if subsequent event read the most
recent value written.

\begin{spec}
writeObservation :: History -> Bool
writeObservation 
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
\end{spec}
The last piece for our implementation of a markability test is function |readPreservation|, which builds a
mapping between variables and values in order to ensure a value read by a transaction isn't overwritten before
it commits.
\begin{spec}
readPreservation :: History -> Bool
readPreservation h
  = all (fst . foldr step (True, Map.empty)) h'
    where
      step (IRead _ v val) (ac,m)
        = case Map.lookup v m of
             Nothing   -> (ac , Map.insert v  (Val 0) m)
             Just val' -> (ac && val == val' , Map.insert v val' m)
      step (IWrite _ v val) (ac,m)
        = case Map.lookup v m of
             Nothing   -> (ac , Map.insert v val m)
             Just val' -> (ac , m)
      step _ ac = ac       
      h' = [ l | l <- splits h
               , isCommit (last l) ]
      isCommit (ICommit _) = True
      isCommit _ = False
\end{spec}
{1,1,0.2}{His research interests include type theory, formal
verification, programming language design and implementation and
category theory.#1}}
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

%\ColourStuff

\MonochromeStuff

\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\black{\mathsf{#1}}}
\newcommand{\TC}[1]{\purple{\mathsf{#1}}}

%subst comment a = "\orange{\texttt{--" a "}}"

\newcommand{\TStep}[9]{\ensuremath{\langle  #2, #3, #4 \rangle
    \mapsto_{T_{#5}} \langle  #7, #8, #9 \rangle}}


\begin{document}


\title{A Property Based Testing Approach for Software Transactional Memory Safety}

\author{Rodrigo Ribeiro \\
Universidade Federal de Ouro Preto \\
Ouro Preto, Minas Gerais --- Brazil\\
rodrigo{@@}decsi.ufop.br
\and
Andr\'e Du Bois\\
Universidade Federal de Pelotas\\
Pelotas, Rio Grande do Sul --- Brazil\\
dubois{@@}inf.ufpel.br}

\maketitle

\begin{abstract}
Software Transactional Memory (STM) provides programmers with a simple high-level model of transactions that allows the
writing of concurrent programs without worrying with locks, since all transaction concurrency management is done by
the STM runtime. Such programming model greatly simplifies development of concurrent applications, but it has a cost:
implementing an efficient and correct STM algorithm is an art. To reduce time wasted on proving safety properties for
unsafe algorithm definitions, we propose use modern random testing techniques for finding counterexamples during
the design process. We use QuickCheck, a property-based random testing library for Haskell, to test
two well-known STM algorithms represented as a small-step semantics over a simple language with STM-Haskell like primitives
with respect to a STM safety property, namely opacity.
\end{abstract}

\keywords{Software Transactional Memory, Semantics, Opacity, Property-based Testing}

\runninghead{R. Ribeiro, A. Du Bois}{A Property Based Testing Approach for Software Transactional Memory Safety}

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
%format PAtomic = "\C{PAt}"
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
%format unId = "\C{unId}"
%format Float = "\D{Float}"
%format transferMoney = "\F{transferMoney}"
%format atomically = "\F{atomically}"
%format writeTVar = "\F{writeTVar}"
%format readTVar = "\F{readTVar}"


\section{Introduction}

Transactional Memory (TM)~\cite{Herlihy1993,Shavit1995} provides programmers a high level concurrency
control abstraction. Programmers can simply declare certain code pieces as
transactions and the TM runtime guarantees that transactions execute in isolation.
The use of TM provides atomicity, deadlock freedom, composability~\cite{Harris05} and
increases productivity when compared to using locks~\cite{Pankratius2011}. Several works developed
software~\cite{Herlihy2003,Herlihy2006,Dice06}, hardware~\cite{Hammond2004} and software / hardware hybrids~\cite{Baugh2008,Dalessandro2011}
implementations. Gradually, industry is adopting TM: IBM Blue Gene/Q processor supports TM and Intel Haswell microarchitecture
supports transaction synchronization primitives~\cite{TSX,Haring2012}.

The TM runtime is responsible to ensure correct management of shared state. Therefore,
correctness of TM clients depend on a correct implementation of TM algorithms. However,
this simple programming model has a price: designing a correct TM algorithm is an art.
Researchers use different techniques to implement the TM interface efficiently. Algorithms
try to interleave transactions as much as possible, while guaranteeing a non-interleaving
semantics. Thus, subtle but fast algorithms are favored over simpler ones and such subtlety
makes them prone to intricate bugs.


A first step towards correct implementation of TM algorithms is a specification of what
is correctness for TM. Intuitively, a correct TM algorithm should guarantee that every
execution of an arbitrary set of transactions is indistinguishable from a sequential
running of them. Several correctness criteria where proposed in the
literature~\cite{Guerraoui2008,Doherty2009,Imbs2009,LesaniP14} and
they rely on the concept of transactional histories. Intuitively,
a history consists of a sequence of operations executed on shared objects
during a TM execution. Analysing TM history structure generated by algorithms,
we can ensure that its TM interface provides atomicity and deadlock freedom to client
applications. However, certify that a TM algorithm is safe according to some criteria
is a non-trivial task. Different works use I/O automata~\cite{Lesani2012}, model
checking~\cite{CohenPZ08,cohen2007,Guerraoui2008a} or define a specification language that
reduces the problem of proving non-opacity of a TM algorithm to SMT solving~\cite{Lesani2013,DeMoura2008}.

Such correctness concerns are not just formalization curiosity, they can influence directly on implementation efficiency.
Le et.al.~\cite{Le2016} mention that current STM-Haskell implementation (which is unsafe w.r.t. the opacity safety criteria)
can cause threads to loop, due to accessing an inconsistent memory view. To avoid such problems STM-Haskell
implementation validates the read set each time a thread is scheduled and such checking overhead cause
a waste of execution time. This is one of the motivation for Le et. al.~\cite{Le2016} proposing a new
implementation of STM-Haskell using the Transaction Locking II (TL2) algorithm~\cite{Dice06}. 

Semanticists have devoted attention to formally specify TM behavior~\cite{Moore2008,Koskinen2010,Abadi2011,Harris05}.
Harris et. al. specifies STM support to Haskell programming language as an extension of GHC compiler~\cite{Harris05},
defines a semantics for a core functional language with STM features and they argue that their semantics is ``small-step'',
but when evaluating an |orElse| operation or a |atomically| block, the semantics uses ``multi-steps'' to evaluate such constructs
using the reflexive-transitive closure of single step semantics. Moore et. al. specifies a small-step semantic for TM providing
textual proofs of some safety properties, but their semantic does not provide support for high-level transactional primitives
like |orElse| and |retry|~\cite{Moore2008}. Hu et. al. uses property based testing for checking a compiler from a high level
STM language to a transactional virtual machine by defining a stop-the-world semantics for the high-level language and a semantics
for the virtual machine~\cite{Hu08}. Hu et. al. high-level semantics also uses multi-steps to evaluate transactions and does not
provide support for high-level operators like |orElse| and |retry|. Schmidt et.al. describes a two semantics for STM-Haskell:
a big-step, which have some undecidable conditions, and a small-step which uses the big-step as a specification and prove the relevant
properties for stabishing the correctness of the small-step semantics w.r.t. the big-step~\cite{Schmidt2013}. Also, Schmidt et. al.
uses its small-step semantics to implement a STM-Haskell library in Haskell programming language and they mention that such correctness
proof between their semantics implies opacity and other safety properties. No proof of such claim is given.

To the best of our knowledge, besides Schimidt et. al work~\cite{Schmidt2013}, there is no truly small-step semantics for TM such that
consider high-level constructs like |orElse| and |retry| while allowing the interleaving of executing transactions. Also, as far we know, there
is no work that uses a trace-based small-step semantics that produces the history of TM execution, which can be used to verify
TM safety properties. This work aims to fill this gap. Our approach is to specify STM algorithms using a standard small-step operational semantics
for a simple transactional language and use property based testing to check if safety properties are satisfied by generated histories.
We are aware that using automated testing isn't sufficient to ensure correctness of an algorithm, but it can expose bugs before spent time
on doomed attempts to certify the semantics within a proof assistant.

Specifically, we made the following contributions:

\begin{itemize}
   \item We define a simplified model language that supports high-level TM constructs 
         |orElse| and |retry| present in STM-Haskell and two trace based small-step operational semantics for it.
         One semantics closely follows the well-known TL2 algorithm~\cite{Dice06} and the other is based on the
         semantics adopted by STM Haskell~\cite{Harris05}.
         These semantics are implemented in the Haskell programming language.
   \item We define TM safety conditions, namely opacity~\cite{Guerraoui2008,Doherty2009},
         in Haskell and check them using QuickCheck~\cite{Claessen00} against the implemented
         semantics. Defining safety properties is just a matter to define functions that verify them on
         histories produced by interpreters implementing TM algorithm semantics.
   \item We show how to QuickCheck generators to implement different test case strategies to improve coverage
         of the semantics implementation and to provide shorter counter-examples. Following~\cite{Hritcu2013}, we
         introduce some bugs in our semantics and check how such different test generation algorithms are
         effective on finding these errors.
\end{itemize}

The rest of this paper is organized as follows. Section \ref{sec:stm-haskell} presents a brief introduction
to software transaction memory, specially its implementation in the Haskell programming language. Section \ref{sec:stm-model}
defines the syntax (Section \ref{sec:stm-syntax}) and operational semantics
based on TL2 and on STM-Haskell (Section \ref{sec:stm-semantics}) for a small STM-Haskell like language.
In Section \ref{sec:stm-safety} we present Haskell implementations of TM safety properties and describe how to check them using
QuickCheck, giving some details on how to build random test cases to improve test coverage results and to find injected bugs in
our semantic definitions~\cite{Hritcu2013}.
Section \ref{sec:related} discuss related work and Section \ref{sec:conclusion} concludes and
presents future work.

All code described in this paper was developed using GHC-8.2.1 and it is available on-line~\cite{stm-rep}.

\section{Software Transaction Memory}\label{sec:stm-haskell}

\paragraph{STM design space:}
In an STM system, memory transactions can execute concurrently and, if finished without conflicts, a transaction may commit.
Conflict detection may be \emph{eager}, if a conflict is detected the first time a transaction accesses a value, or \emph{lazy}
when it occurs only at commit time. With eager conflict detection, to access a value, a transaction must acquire ownership of
the value, hence preventing other transactions to access it, which is also called pessimistic concurrency control. With optimistic
concurrency control, ownership acquisition and validation occurs only when committing. These design options can be combined for
different kinds of accesses to data, e.g., eager conflict detection for write operations and lazy for reads. STM systems also
differ in the granularity of conflict detection, word based and object based being the most common. 
STM systems need a mechanism for version management. With eager version management, values are updated directly in memory and a
transaction must maintain an undo log where it keeps the original values. If a transaction aborts, it uses the undo log to copy
the old values back to memory. With lazy version management, all writes are buffered in a redo log, and reads must consult this
log to see earlier writes. If a transaction commits, it copies these values to memory, and if it aborts the redo log can be discarded.
An STM implementation can be lock based, or obstruction free. An obstruction free STM does not use blocking mechanisms for
synchronization and guarantees that a transaction will progress even if all other transactions are suspended. Lock based
implementations, although offering weaker progress guarantees, are believed to be faster and easier to implement.

TL2 is a classic lock based, deferred update transactional algorithm, similar to the one used in the GHC implementation of
STM Haskell~\cite{Harris05}: all writes are recorded in a write-set. When a transaction finishes, it validates its log to
check if it has seen a consistent view of memory, and its changes are committed to memory. The main difference of the TL2
algorithm is that conflicts are detected by using a global clock that is shared by all threads. When a transaction starts executing
it reads the global clock to get its read stamp. Every transacted memory
location is associated with a write stamp, when opening an object for reading/writing, the transaction checks
if the write stamp of memory address is not greater than the transaction read stamp, in that case it means that the object
was modified after the transaction started executing, hence the transaction must be aborted. If the memory passes the validation
it means that the transaction has seen a consistent view of the memory.

\paragraph{STM Haskell:}Harris et.al.~\cite{Harris05} extends Haskell with a set of primitives for writing memory transactions.
The main abstractions are transactional variables or |TVar|s, which are special variables that can only
be accessed inside transactions. Below, the main STM Haskell primitives are shown. The |readTVar| takes
a |TVar| and returns a transactional action |STM a|. This action, when executed, will return a value of
type |a|, i.e., the |TVar|'s content. Similarly, |writeTVar| takes a value of type |a|, a |TVar| of the
same type and returns a STM action that when executed writes into the |TVar|.

\begin{spec}
data TVar a = ...
data STM a = ...

writeTVar :: TVar a -> a -> STM ()
readTVar :: TVar a -> STM a
retry :: STM ()
orElse :: STM a -> STM a -> STM a
atomically :: STM a -> IO a
\end{spec}

These transactional actions can be composed together to generate new actions through
monadic combinators or the do notation:

\begin{spec}
type Var = TVar Float

transferMoney :: Float -> Var -> Var -> STM ()
transferMoney amount acc1 acc2 =  do
    v <- readTVar acc1
   if v >= amount
    then do
          writeTVar acc1 (v-amount)
          v2 <- readTVar acc2
          writeTVar acc2 (v2+amount)
    else retry
\end{spec}
The |retry| primitive is used to abort and re-execute a transaction once at least one of the
memory positions it has read is modified and |orElse| is a choice operator, it takes two transactions
as arguments, if the first one retries then the second one is executed. If both fail the whole
transaction is executed again. Transactions are executed with |atomically|:
\begin{spec}
atomically (transferMoney 100.00 tvar1 tvar2)
\end{spec}
It takes as an argument a transactional action (|STM a|) and executes it atomically with
respect to other concurrently executing transactions.

\section{A Model for Software Transactional Memory}\label{sec:stm-model}

Our objective is to formalize semantic that ensure, by construction, that an
implementation for transactional memory enjoy safety properties, namely opacity and markability. 

\subsection{Language Syntax}\label{sec:stm-syntax}

Our minimalistic language is defined by data types |Tran|, which
represents computations in the |STM| monad, and |Proc| that denotes
actions in the Haskell |IO| monad. This language is, in essence,
the same as the one proposed by~\cite{Hu08}. We extend it with
|orElse|, |retry|, conditional constructs and a special value to
denote a aborted transaction, |TAbort|. Such constructs aren't
an essential part of a model for TM, but they are interesting
on their own when we consider safety properties of TM.

\begin{spec}
newtype Val = Val { unVal :: Int }

newtype Var = Var { unVar :: Int }

newtype Id = Id { unId :: Int }

data Tran = TVal Val | TRead Var | TWrite Var Tran
| Tran :+: Tran | TIf Tran Tran Tran
| TOrElse Tran Tran | TRetry | TAbort

data Proc = PVal Val | PFork Proc
| PAtomic (Maybe (Id,Stamp)) Tran
| Proc :++: Proc
\end{spec}

In order to avoid dealing with name binding, we do
not provide a language construct for creating new
variables and also use addition operation for
composing transactions and processes. This is valid simplification,
since addition forms a monoid on integer values, while still retaining
the sequencing computations and combining their results. %% rewrite to emphasize that monads are monoids
We represent variables and values by integers (properly
wrapped using a |newtype|). Each syntax construct meaning
is immediate with the exception of how we represent atomic blocks. A value built with constructor
|PAtomic| carries information about its transaction id and current
transaction read stamp. Initially, all |PAtomic| values are built using
|Nothing| to denote that such block did not started its execution.
To avoid clutter in the presentation of |PAtomic| semantics, we represent
information about transaction id and read stamp as $(i,j)$ whenever it
has the form |Just| $(i,j)$ and as $()$ if it is equal to |Nothing|. Also,
we allow ourselves a bit of informality and write |Id|s, |Stamp|s, |Val|
and |Var| values as if they were simple integers.

Construction |TAbort| is used to represent a transaction
that is aborted by accessing an inconsistent view of memory,
in our TL2-based semantics, and by trying to commit an transaction that
which has accessed and invalid memory configuration, in STM-Haskell based semantics.
Term |TAbort| does not appear on randomly
generated source programs.
It is used in our semantics to properly
differ between different types of transaction aborting and how
they should be treated by semantics of |orElse| construct, since
transactions aborted by inconsistent views should not be captured
by an |orElse|.

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

\begin{example}
As an example of how our tiny language can model STM constructs,
consider the following function that increments a value stored on a |TVar|,
if it is different from zero.

%format incVar = "\F{incVar}"

\begin{spec}
  incVar :: TVar Int -> STM ()
  incVar v
     = do
         x <- readTVar v
         if x == 0 then return ()
           else writeTVar v (x + 1)
\end{spec}

Such function can be represented in our language as follows:

\begin{spec}
   incVar v = TIf (TRead v) 0 (TWrite v (TRead v :+: 1))
\end{spec}
\end{example}

\subsection{Language Semantics}\label{sec:stm-semantics}

In this section, we define two operational semantics for our STM language. First, we
present a semantics inspired by the TL2 algorithm which unlike previous works~\cite{Harris05,Hu08}
uses heaps, transaction logs (read and write sets) and also records the event history of current
TM execution. The use of transaction logs on a high-level semantics is a bit unusual, but necessary
to proper modeling of commit and abort operations of different TM algorithms. Next, we propose a
semantics inspired by STM Haskell in which no global clock is used for |TVar| version control.

%% explicitly mention that we will present semantics using math, but it is implemented as
%% haskell functions. We use math to provide a concise notation.

%Following common practice, notation $h\,[x\mapsto v]$ denotes
%finite mapping update, i.e. finite mapping $h'$ such that:
%1) $h'(x) = v$ and 2) $h'(y) = h(y)$, for $x \neq y$.
%To avoid notation clutter, w

Before presenting the semantics, we need to define some notation.
We use finite maps to  represent heaps and logs used by transactions (i.e. read and write
sets). Notation $\bullet$ denotes an empty finite mapping and
$\Theta$ represents a 4-tuple formed by a heap and mappings between transaction id's and their
read / write sets and transactions. We let $\Theta_h$, $\Theta_r$, $\Theta_w$, and $\Theta_T$ represent the heap and finite
functions between transaction ids and their logs and transactions,
respectively. Let $h(x)$ denote the operation
of retrieving the value associated with key $x$ in finite mapping 
$h$ and $h(x)=\bot$ denotes that no value is associated
with $x$. Notation $h \uplus h'$ denotes the right-biased union of 
two finite mappings, i.e. when both maps have the same key $x$, we keep
the value $h'(x)$. We let $\Theta_r(x,j)$ denote the operation of
retrieving the value associated with key $x$ in the read set of transaction
with id $j$. Notation $\Theta_w(x,j)$ is defined similarly for write sets. Updating
a variable $x$ with value $v$ in the read set of transaction $j$ is denoted as
$\Theta_r\,[j,x\mapsto v]$. Same holds for write set $\Theta_w$.
Finally, notation $h\mid_{x}$ denotes the finite mapping $h'$ with entries for the key $x$
removed, i.e. $h' = h - [ x \mapsto v]$, for some value $v$.

%format Item = "\D{Event}"
%format Stamp = "\D{Stamp}"
%format IRead = "\C{IRead}"
%format IWrite = "\C{IWrite}"
%format IBegin = "\C{IBegin}"
%format ICommit = "\C{ICommit}"
%format IAbort = "\C{IAbort}"
%format IRetry = "\C{IRetry}"
%format History = "\D{History}"

Operations executed on transactional variables during a TM
execution are represented by data type |Item|. Essentially,
|Item| records operations on variables and on transactions.
A history of a TM execution is formed by a list of |Item|s.
\begin{spec}
newtype Stamp = Stamp { unStamp :: Int }

data Item = IRead Id Var Val
          | IWrite Id Var Val
          | IBegin Id  
          | ICommit Id
          | IAbort Id
          | IRetry Id

type History = [Item]
\end{spec}
Data type |Stamp| denotes the global clock used by the TL2 algorithm to ensure correct variable versions.
Constructors |IBegin|, |ICommit| and |IAbort| denote the beginning, commit and failure of
a transaction with a given |Id|. We consider that a transaction fails
when it tries to read from an inconsistent view of memory. |IRead id v val| records that
value |val| was read by transaction |id| for variable |v| and |IWrite id v val|
denotes that value |val| was written in variable |v| by transaction |id|.
An event |IRetry| denotes the user called |retry| on current transaction and such
transaction should be restarted. In our semantics, the computation of histories is represented
as a Writer monad, which adds a new element by appending at history end. But, for presentation
purpouses, we simply add a new event at head of a given history.

\subsubsection{TL2 Based Semantics}

Now, we present our semantics based on Transactional Locking 2 
algorithm~\cite{Dice06}. Informally, TL2 algorithm works as follows:
threads execute reads and writes to objects, but no memory locations are actually modified. All 
writes and reads are recorded in write and read logs. When a
transaction finishes, it validates its log to check if it has seen a 
consistent view of memory, and its changes are committed to memory.

Function $\Theta(x,i,j)$ denotes that transaction $j$ with read-stamp $i$ tries to
to read the content of variable $x$ and it works as follows:
First it checks the write set. If the variable has not been written to, the read set is consulted.
Otherwise, if the variable has also not been read, its value is looked up from the heap and the read log updated accordingly, if
variable's write stamp is not greater than current transaction read-stamp $i$. Otherwise, we have an conflict and the current
transaction is aborted by returning |TAbort|.

\begin{figure}[h]
  \[
  \Theta(x,i,j) = \left\{
  \begin{array}{ll}
     (v,\Theta) & \textit{if }\:\Theta_w(x,j) = (i',v)\\
     (v,\Theta) & \textit{if }\:\Theta_w(x,j) = \bot,\Theta_r(x,j) \neq \bot, \\
                & \:\:\:\:\: \Theta_h(x) = (i',v) \textit{ and } i \geq i'\\
     (v, \Theta_r\,[j,x \mapsto v]) & 
        \textit{if }\:\Theta_w(x) = \Theta_r(x) = \bot,\\
                                       & \:\:\:\:\:  \Theta_h(x) = (i',v),
                                     \textit{ and } i \geq i' \\
                           |TAbort| & \textit{if }\: \Theta_h(x) = (i',v)
                                    \textit{ and } i < i'
  \end{array}
                                  \right.
  \]
  \centering
  \caption{Reading a variable}
  \label{fig:readvar}
\end{figure}

Predicate $consistent(\Theta,i,j)$ holds if transaction $j$ has finished its execution
on a valid view of memory. We say that a TM state $\Theta$ is consistent if all variables read
have stamps less than or equal to $i$, the global clock value in which transaction $j$ have started.

\begin{figure}[h]
  \[
     consistent(\Theta,i,j) = \forall x. \Theta_r(x,j) = (i,v) \to
     \Theta_h(x) = (i',v) \land i \geq i'
  \]
  \centering
  \caption{Predicate for consistency of transaction logs}
  \label{fig:consistency}
\end{figure}

%format TFail = "\C{TFail}"
%format IFail = "\C{IFail}"

In order to provide a concise semantics definition, in Figure~\ref{fig:hole-syntax},
we define evaluation contexts to avoid the need of ``congruence rules''. In our
semantics definition we use the following meta-variable convention: we let $t$
denote arbitrary transactions and $p$ processes. Values are represented by $v$,
stamps by $i$ and transaction ids by $j$. All meta-variables can appear primed or subscripted, as
usual. Finally, in order to avoid several rules to propagating different types of
transaction failure, we use |TFail| whenever any of |TAbort| or |TRetry| applies.
Same holds for events: |IFail| will represent any of |IAbort| or |IRetry|.  

\begin{figure}[h]
        \[
              \begin{array}{c}
                   \textit{Evaluation contexts for transactions} \\
                   \\
                   \begin{array}{rcl}
                      \EvalCtxTran{\cdot} & ::=    & |TWrite|\, v\:\EvalCtxTran{\cdot}\\
                                                   & \mid &\EvalCtxTran{\cdot}\: |:+:| t\\
                                                   & \mid & |TVal|\,v |:+:| \EvalCtxTran{\cdot}\\
                                                   & \mid & |TIf|\:\EvalCtxTran{\cdot}\:t\:t' \\
                                                   & \mid & |TOrElse|\:\EvalCtxTran{\cdot}\:t\\
                   \end{array}
                    \\
                \\
                    \textit{Evaluation contexts for processes}\\
                    \\
                    \begin{array}{rcl}
                      \EvalCtxProc{\cdot} & ::=    & |PFork|\:\EvalCtxProc{\cdot}\\
                                                   & \mid &\EvalCtxProc{\cdot}\:|:++:| t\\
                                                   & \mid & |PVal|\,v\,|:++:|\EvalCtxProc{\cdot}\\
                                                   & \mid & |PAtomic|\,(|Just|\, (i,j))\:\EvalCtxProc{\cdot}
                    \end{array}
              \end{array}
        \]
        \centering
        \caption{Evaluation contexts for high-level language.}
        \label{fig:hole-syntax}
\end{figure}

\paragraph{Transaction Semantics:}

We define transaction semantics by a reduction relation $\mapsto_{T_{i\,j}}$ on triples
$\langle \Theta, \sigma, t \rangle$, where $\Theta$ is the current state of TM,
$\sigma$ is the history of TM execution and $t$ is a transaction. Variables $i$ and $j$
denote the current transaction read stamp and id, respectively. First, we present
the rule used to evaluate transaction contexts.

\[
  \infer[_{(TContext)}]
        { \langle \Theta,\,\sigma,\,\EvalCtxTran{t}\rangle \mapsto_{T_{i\,j}}
          \langle \Theta',\,\sigma',\,\EvalCtxTran{t'}\rangle }
        { \langle \Theta,\,\sigma,\,t \rangle \mapsto_{T_{i\,j}}
          \langle \Theta',\,\sigma',\, t'\rangle }
\]

This rule simply allows stepping some subterm of current transaction expression $\EvalCtxTran{t}$.

Next, we will consider how to evaluate a |TRead| construct. Notice that, 
we need two different rules for reading variables. This happens because, in our semantics, the
function that reads a value from a variable can abort the current transaction, as it happens in TL2,
if its write stamp is less than current transactions read stamp.

\[
\begin{array}{c}
  \infer[_{(TReadOk)}]
        { \langle \Theta,\, \sigma, |TRead|\,v \rangle \mapsto_{T_{i\,j}}
          \langle \Theta',\, \sigma',\,|TVal|\,val\rangle }
        {\Theta(v,i,j) = (val,\Theta') & \sigma' = |IRead|\,j\,v\,val\,:\sigma}
  \\
  \\
  \infer[_{(TReadFail)}]
        { \langle \Theta,\, \sigma, |TRead|\,v \rangle \mapsto_{T_{i\,j}}
          \langle \Theta, \, \sigma',\, |TAbort| \rangle}
        {\Theta(v,i,j) = (|TAbort|,\Theta') & \sigma' = |IAbort|\,j\,:\sigma} 
\end{array}
\]

Writing a value is done by next rules: rule $(TWriteVal)$ writes a completely
reduced value and rule $(TWriteFail)$ just does propagate failure for
signaling that current transaction has failed or aborted throught an explicit
|TRetry|.

\[
\begin{array}{c}
  \infer[_{(TWriteVal)}]
        { \langle \Theta, \, \sigma, |TWrite|\,v\,(|TVal|\,val)\rangle \mapsto_{T_{i\,j}}
          \langle \Theta', \, \sigma',\,|TVal|\,val\rangle}
        {\begin{array}{c}
            \Theta' = \langle \Theta_h, \Theta_r, \Theta_w[j,x \mapsto val], \Theta_T\rangle \\
            \sigma' = |IWrite|\,j\,v\,val\, : \sigma \\
         \end{array}}
  \\ \\
  \infer[_{(TWriteFail)}]
        { \langle \Theta, \,\sigma, |TWrite|\,v\,|TFail|\rangle \mapsto_{T_{i\,j}}
          \langle \Theta, \, \sigma,\, |TFail| \rangle }
        { }
\end{array}
\]

Since we replace monadic bind by addition, we need to
force a sequential order of evaluation and some additional
rules to ensure the correct propagation of
failure.

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

We can evaluate a |TIf| to its first branch if its condition is equal to zero or to its
second otherwise. 

\[
  \begin{array}{c}
     \infer[_{(TIfZero)}]
           {\langle \Theta,\sigma,|TIf|\,(|TVal 0|)\,t\,t'\rangle \mapsto_{T_{i\,j}}
            \langle \Theta,\sigma,\,t\rangle}
           {}
     \\ \\
     \infer[_{(TIfNonZero)}]
           {\langle \Theta,\sigma,|TIf|\,(|TVal v|)\,t\,t'\rangle \mapsto_{T_{i\,j}}
            \langle \Theta,\sigma,\,t'\rangle}
           {v \neq 0}          
  \end{array}
\]

We also propagate failures produced on |TIf| condition evaluation.

\[
  \begin{array}{c}
     \infer[_{(TIfFail)}]
           { \langle \Theta,\,\sigma,\,|TIf|\,|TFail|\,t\,t'\rangle\mapsto_{T_{i\,j}}
             \langle \Theta,\,\sigma,\,|TFail|\rangle }
           {}
  \end{array}
\]

Evaluating a |TOrElse| construct returns a value, if whenever its left transaction
reduces to |TVal v|. Right transaction is executed only when the left one reduces to
|TRetry|. Finally, if a transaction aborts such aborting signal is propagated.

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


\paragraph{Process Semantics:}

The semantics for processes, $\mapsto_{P}$, acts on 5-uples $\langle \Theta,\sigma,j,i,s\rangle$
consisting of a TM state $\Theta$, a history of transaction execution $\sigma$,
last transaction id used $j$, a global clock $i$ and a process soup $s$.

We begin the presentation of process semantics with context rule, which allows
steps of inner expressions.

\[
  \infer[_{(PContext)}]
        { \langle \Theta,\,\sigma,\,j,\,i,\EvalCtxProc{p} : s\rangle \mapsto_{P}
          \langle \Theta,\,\sigma',\,j',\,i',\,\EvalCtxProc{p'} : s\rangle }
        { \langle \Theta,\,\sigma,\,j,\,i,\,t \rangle \mapsto_{P}
          \langle \Theta',\,\sigma',\,j',\,i',\, t'\rangle }
\]

Process soup are represented by a list of processes and its execution proceeds by
pattern matching on the first element of such list. In order to allow non-determinism
we introduce a rule for preemption.

\[
   \infer[_{(PPreempt)}]
         { \langle \Theta,\,\sigma,\,j,\,i,\,p : s\rangle \mapsto_{P}
           \langle \Theta',\,\sigma',\,j',\,i',p : s'\rangle }
         { \langle \Theta,\,\sigma,\,j,\,i,\,s\rangle \mapsto_{P}
           \langle \Theta',\,\sigma',\,j',\,i',\,s'\rangle } 
\]

Evaluating a |PFork| adds a process $p$ to current soup returning $0$.

\[
    \infer[_{(PFork)}]
          {\langle \Theta,\,\sigma,\,j,\,i,\, (|PFork|\,p) : s \rangle \mapsto_{P}
           \langle \Theta,\,\,\sigma,\,j,\,i,\, s' \rangle}
          {s' = |PVal|\,0 : p : s}
\]

As we did with transaction, process composition is done using addition.

\[
\begin{array}{c}
  \infer[_{(Add1)}]
        { \langle \Theta, \, \sigma,\,j,\,i,\, (|PVal|\,v_1) |:++:| (|PVal|\,v_2) \rangle \mapsto_{P}
          \langle \Theta, \, \sigma,\,j,\,i,\, |PVal|\,v \rangle}
        {v = v_1 + v_2}
\end{array}
\]
Finally, we now present the semantics for atomic blocks. Unlike previous works~\cite{Hu08,Harris05},
the semantics of atomic blocks do not follow the so-called stop-the-world-semantics.
This design choice is justified by the fact that stop-the-world semantics naturally enjoys safety conditions
like opacity and markability. Since our objective is to exploit failures in STM algorithms represented as small-step semantics
of our simple transactional language, the proposed semantics reduces atomic blocks in a step-wise manner instead of using
a multi-step approach.

The first rule for reducing a |PAtomic| block is presented below. It basically updates the TM state with empty
read and write sets for the newly started transaction $j$, register it using |IBegin| $j$ and reinsert process
|PAtomic| $(i,j)\,t$ at the end of process soup. Notice that, initially, every atomic block does not have its
read stamp and transaction id. When a transaction $t$ is started, we update its process to store its starting clock and transaction id.

\[
  \begin{array}{c}
  \infer[_{(PAt1)}]
        {\langle \Theta,\,\sigma,\,j,\,i,\,|PAtomic|\,|()|\,t : s\rangle\mapsto_{P}
         \langle \Theta',\,\sigma',\,j + 1,\,i,\, s'\rangle}
        {\begin{array}{c}
         \Theta_1 = \langle \Theta_h, \Theta_r\,[j\mapsto \bullet], \Theta_w\,[j\mapsto \bullet], \Theta_T\,[j\mapsto t]\rangle\\
         s' = s |++| [|PAtomic|\,(i,j)\,t] \\
         \sigma' = |IBegin|\,j : \sigma
         \end{array}}
  \end{array}      
\]

After initializing a transaction, its execution proceeds thanks to rules $PPrempt$ and $PContext$. Whenever a
transaction successfully reduces to a value and it had executed in a consistent view of memory, we can use next
rule to commit its results to heap.

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
We first check consistency using $consistent(\Theta,i,j)$, register a successful commit in history $\sigma$ using
|ICommit| $j$ and update TM state $\Theta$ by: 1) writing the write set contents of transaction $j$ in the heap and
2) removing the read and write set of transaction $j$ from TM state.

Whenever a transaction reduces to |TRetry| or |TAbort| (represented by |TFail|), it should be restarted.
For this, we remove entries for the transaction $j$ from transactions and read / write set mappings.
Also, we reinsert a process with the original transaction in the process soup to allow the restarting
of this transaction. This is specified by next rule.

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

\subsubsection{STM-Haskell Based Semantics}

Essentially, the STM-Haskell based semantics is just a simplification of the previouly defined one in which
we do not take into account the global clock to ensure consistency of transaction logs. This change simplifies
both the semantics and their auxiliar definitions to read variables and check for consistency of TM state.

In Figure~\ref{fig:readvar1}, we redefine the function for reading a value from a variable. Note that this is
almost the definition of Figure~\ref{fig:readvar} except that it does not use a global clock for
version control of variables in read set.

\begin{figure}[h]
  \[
  \Theta(x,j) = \left\{
  \begin{array}{ll}
     (v,\Theta) & \textit{if }\:\Theta_w(x,j) = (i,v)\\
     (v,\Theta) & \textit{if }\:\Theta_w(x,j) = \bot,\Theta_r(x,j) \neq \bot, \\
                & \:\:\:\:\: \Theta_h(x) = (i,v) \\
     (v, \Theta_r\,[j,x \mapsto (i,v)]) & 
        \textit{if }\:\Theta_w(x) = \Theta_r(x) = \bot,\\
                                       & \:\:\:\:\:  \Theta_h(x) = (i,v)
  \end{array}
                                  \right.
  \]
  \centering
  \caption{Reading a variable}
  \label{fig:readvar1}
\end{figure}

Also, since we do not abort current transaction when reading a value from a inconsistent
memory view, the rule $(TReadFail)$ isn't necessary in STM-Haskell based semantics. When writing
values to variables, the only change needed is to increment variable's write stamp.
Modified rule is presented below.

\[
  \begin{array}{l}
  \infer[_{(TWriteVal)}]
        { \langle \Theta, \, \sigma, |TWrite|\,v\,(|TVal|\,val)\rangle \mapsto_{T_{i\,j}}
          \langle \Theta', \, \sigma',\,|TVal|\,val\rangle}
        {\begin{array}{c}
            \Theta' = \langle \Theta_h, \Theta_r, \Theta_w[j,x \mapsto (i',val)], \Theta_T\rangle \\
            \sigma' = |IWrite|\,j\,v\,val\, : \sigma \\
         \end{array}}
  \end{array}
\]


We also need to modify the consistency check. In the original STM-Haskell paper~\cite{Harris05}, consistency
of TM state is tested before a commit in order to validade if a transaction has accessed a valid memory view.
This validity test essentially checks pointer equalities for values in read set. Since in our model we have no
notion of pointer, we use value equality for consistency check as in~\cite{Hu08}.
\begin{figure}[h]
  \[
     consistent(\Theta,j) = \forall x. \Theta_r(x,j) = \Theta_h(x)
  \]
  \centering
  \caption{Predicate for consistency of transaction logs}
  \label{fig:consistency1}
\end{figure}

Semantics for transactions and processes are essentially the same presented in previous section. Rules will
differ only by: 1) Information about TL2 global clock isn't present and 2) it uses the modified consistency
check and reading values from the TM state function presented in this section. For space reasons, we do not
present this slightly modified set of semantic rules.

\section{Safety Properties}\label{sec:stm-safety}

Several safety conditions for TM were proposed in the literature, such as opacity~\cite{Guerraoui2008},
VWC~\cite{Imbs2009}, TMS1 and TMS2~\cite{Doherty2009} and markability~\cite{LesaniP14}. All these conditions define
indistinguishably criteria and the set of correct histories generated by the execution of TM. In this section, we
present a Haskell implementation of opacity. The choice of using opacity over other safety properties is motivated
by the fact that we can implement it from its informal definition instead of using
a graph based characterization of the structure of histories generated by a TM algorithm~\cite{Gueraoui2008}.

Before we give the definition and implementation of opacity, we need to define some concepts. We say that a transaction
is \emph{live} in a history $H$ if it has no commit or abort registered in $H$, otherwise it is \emph{finished}. A history is said to be \emph{legal}
if all values read after a write in transactional variable are equal to last value written.

\subsection{Opacity}

%format opacity = "\F{opacity}"
%format History = "\D{History}"
%format all     = "\F{all}"
%format finalStateOpacity = "\F{finalStateOpacity}"
%format inits = "\F{inits}"
%format Bool = "\D{Bool}"

Intuitively, if a TM algorithm has the opacity property it means that all histories produced by it are legal and
preserves the real time ordering of execution, i.e. if a transaction $T_i$ commits and updates a variable $x$ before
$T_j$ starts then $T_j$ cannot observe that old state of $x$. Guerraoui et.al. define formally opacity and provide a
graph-based characterization of such property in a way that an algorithm is opaque only if the graph built from algorithm
histories structure is acyclic~\cite{Guerraoui2008}. In this work, we use a more direct encoding of opacity by representing it
as a predicate over histories. We implement such predicate as a Haskell function following the textual definition
present in~\cite{Guerraoui2010}.

We say that a TM algorithm is opaque if all prefixes of histories generated by it are final state opaque.
Our Haskell definition of opacity is as follows:
\begin{spec}
opacity :: History -> Bool
opacity = all finalStateOpacity . inits
\end{spec}
Function |all| checks if all elements of input list (second parameter) satisfy a predicate (first paremeter) and
|inits| returns a list with all prefixes of a given list.

Our next step is to define when a history is final state opaque. We say that a finite history is final state opaque if
exists some completion of it that preserves real time order and all of its transactions are legal.
In Haskell code:

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

\begin{spec}
finalStateOpacity :: History -> Bool
finalStateOpacity
  = some prop . completions
    where
      prop tr = preservesOrder tr && legal tr
      some p xs = (null xs) || (any p xs)
\end{spec}

Function |completions| produces a list of all completions of a
given history. The completion of a history $H$ is another history $S$, such that:
\begin{itemize}
  \item All live and non-commit pending transactions of $H$ are aborted in $S$; and
  \item All commit pending transactions of $H$ are aborted or committed in $S$.
\end{itemize}
Since in our model we do not consider commit-pending transactions, completion of a history consists of aborting all
live transactions. In order to abort all live transactions we have to split a history in sub-histories that group
operations by transactions. This is done by function |splits|, which build a map between transaction ids and history items
and return a list of histories, one for each transaction.
%format Map = "\D{Map}"
%format elems = "\F{elems}"
%format step = "\F{step}"
%format empty = "\F{empty}"
%format maybe = "\F{maybe}"
%format insert = "\F{insert}"
%format lookup = "\F{lookup}"
%format last = "\F{last}"
%format isCommit = "\F{isCommit}"
%format True = "\C{True}"
%format False = "\C{False}"
%format finished = "\F{finished}"
%format completed = "\F{completed}"
\begin{spec}
splits :: History -> [History]
splits
  = Map.elems . foldr step Map.empty
    where
      step i ac
         = maybe (Map.insert (stampOf i) [i] ac)
                 (\ is -> Map.insert (stampOf i)
                                     (i : is)
                                     ac)
                 (Map.lookup (stampOf i) ac)
\end{spec}
Using |splits|, the definition of |completions| is immediate: we just abort each non-committed transaction and
remove them together with failed ones. Checking if a sub-history for a transaction is comitted or not is a simple
check if the last item of sub-history is equal to |ICommit| or not.
\begin{spec}
completions :: History -> [History]
completions 
  = foldr abortLives [] . splits
    where
      abortLives tr ac
        | finished tr = tr : ac
        | otherwise = ac

completed :: History -> Bool
completed
  = finished . last
    where
      finished (ICommit _) = True
      finished (IAbort _)  = True
      finished _           = False
\end{spec}
To finish the implementation of |finalStateOpacity|, we need to present definitions of |preservesOrder| and
|legal|. The function that verifies if a history preserves \emph{real time ordering} is |preservesOrder|. Let $t_k$ and
$t_m$ be transactions of some history $H$. We say that $t_k \prec_H t_m$, if whenever $t_k$ is completed and
the last event of $t_k$ precedes the first event of $t_m$ in $H$. A history $H'$ preserves the real time ordering
of $H$ if for all transactions $t_k$ and $t_m$, if $t_k \prec_{H} t_m$ then $t_k \prec_{H'} t_m$. Intuitively,
function |preservesOrder| checks if transaction ids are ordered according to its position in history. 
%format and = "\F{and}"
%format zipWith = "\F{zipWith}"
%format sequentialSpecs = "\F{sequentialSpecs}"
%format isLegal = "\F{isLegal}"
%format fst = "\F{fst}"
%format readOrWrite = "\F{readOrWrite}"
%format mapMaybe = "\F{mapMaybe}"
\begin{spec}
preservesOrder :: History -> Bool
preservesOrder tr
  = and [ i <= i' | (p,  i)  <- tr',
                    (p', i') <- tr',
                    p <= p']
    where
      tr' :: [(Int, Stamp)]
      tr' = zipWith step [0..] tr
      step p i = (p,(stampOf i))
\end{spec}
In order to check if all events of a transaction are legal we build a map between variables
and events of read and writing to them using function
|sequentialSpecs| which, in turn, uses function |readOrWrite| that returns a variable plus
the event itself or |Nothing|, if it was not a read or write event.
\begin{spec}
readOrWrite :: Item -> Maybe (Var,Item)
readOrWrite i@(IRead _ v _)
  = Just (v,i)
readOrWrite i@(IWrite _ v _)
  = Just (v,i)
readOrWrite _
  = Nothing

sequentialSpecs :: History -> [History]
sequentialSpecs 
  = Map.elems . step1 . mapMaybe readOrWrite
    where
      step1 = foldr step Map.empty
      step (v,i) ac
         = maybe (Map.insert v [i] ac)
                 (\is -> Map.insert v (i:is) ac)
                 (Map.lookup v ac)
\end{spec}
Finally, function |legal| checks if all values read for a variable are equal to last value written, by
folding over the list of events built for each variable by function |sequentialSpecs|.
\begin{spec}
legal :: History -> Bool
legal
  = all isLegal . sequentialSpecs
    where
      isLegal = fst . foldr step (True,Map.empty)
      step (IRead _ v val) (c,m)         
         = maybe (val == (Val 0), m)     
                 ((,m) . (c &&) . (== val))
                 (Map.lookup v m)
      step (IWrite _ v val) (c,m)
        = (c,Map.insert v val m)
      step _ ac = ac
\end{spec}

Opacity can be characterized by building a graph over the set of generated histories by a TM algorithm. Such
proof for the TL2 algorithm can be found in~\cite{Guerraoui2010}.

\section{Validation of Semantic Properties}

%% here we should mention the properties tested as haskell code or
%% use math notation. Also, we should put code coverage in context with
%% properties tested.

%% explain code coverage gaps

After the presentation of language semantics and the implementation of
opacity in terms of execution histories, how can we
be sure that the defined semantics enjoys and the compiler preserves these
properties? We follow the lead of~\cite{Hu08} and use QuickCheck~\cite{Claessen00} to
generate random high-level programs and check them against the opacity property.

Each of these properties have been implemented as Haskell functions and tested using QuickCheck for randomly test cases.
Having running many thousands of tests, we gain a high degree of confidence in the safety of our semantics, but it is
important to measure how much of code base is covered by the test suite. Such statistics are provided by Haskell Program Coverage
tool~\cite{Gill2007}. Results of code coverage are presented in the next figure.

\begin{figure}[!htb]
\centering
\includegraphics[scale=0.38]{coverage.png}
\caption{Test Coverage Results}
\label{fig:test-coverage}
\end{figure}
%format Arbitrary = "\TC{Arbitrary}"
%format arbitrary = "\F{arbitrary}"
%format genProc = "\F{genProc}"
%format sized = "\F{sized}"
%format frequency = "\F{frequency}"
%format div = "\F{div}"
%format Gen = "\D{Gen}"
%format <$> = "\F{\,\langle\$\rangle\,}"
%format <*> = "\F{\,\langle *\rangle\,}"
While not having 100\% of code coverage, our test suite provides a strong evidence that proposed semantics enjoys
safety properties by exercising on randomly generated programs of increasing size. By analysing test coverage
results, we can observe that code not reached by test cases consists of stuck states on program semantics.

For generating random programs
we use basic generators provided by QuickCheck library and build |Arbitrary| instances for |Tran| and |Proc| types.
Below, we present a snippet of instance for |Proc|. Code for |Tran| follows the same structure.
\begin{spec}
instance Arbitrary Proc where
  arbitrary
    = sized genProc

genProc :: Int -> Gen Proc
genProc n
   | n <= 0 = PVal <$> arbitrary
   | otherwise
       = frequency
           [
             (n + 1, PVal <$> arbitrary)
           , (n2, PFork <$> genProc (n - 1))
           , (n2, PAtomic Nothing<$> arbitrary)
           , (n, (:++:) <$> genProc n2 <*> genProc n2)
           ]
     where
       n2 = div n 2
\end{spec}
The |sized| function allows for generating values with a size limit and |frequency| creates a generator
that chooses each alternative with a probability proportional to the accompanying weight.

The TL2-based semantics passed in all tests for safety properties, as expected, since it is well-known
that TL2 provides opacity. But, the semantics based on STM-Haskell does not enjoy such safety properties
since it allows the reading from an inconsistent view of memory. Next example shows how such invalid
memory access can happen.

\begin{example}
Consider the following program, where |x| is some variable:
\begin{spec}
t1 :: Tran
t1 = TRead x :+: TRead x :+: TRead x

t2 :: Tran
t2 = TWrite x v

p :: Proc
p = Fork (PAtomic Nothing t1) :++: Fork (PAtomic Nothing t2)
\end{spec}
One of the possible executions of |p| using STM-Haskell semantics would result in the following
history:
\begin{spec}
   [ IBegin 1, IBegin 2, IRead 1 x 0
   , IWrite 2 x 10, IRead 1 x 0, ICommit 2
   , IRead 1 x 0, ...]
\end{spec}
which violates opacity and markability because it does allow transaction |t1| to read from an inconsistent
memory view. On TL2 semantics safety is preserved because when transaction |t1| tries to execute third read
it would be aborted.
\end{example} 

\section{Related Work}\label{sec:related}

\paragraph{Semantics for STM:}
Semantics for STM have been received a considerable attention recently~\cite{Harris05,Abadi2011,Moore2008,Liblit06}.
Harris et al.~\cite{Harris05} defines a stop-the-world operational semantics for STM Haskell.
Essentially, Harris uses a multi-step execution model for transaction execution that does not
allows the investigation of safety property neither how interleaving of transactions happens.
Such approach for STM semantics does not allows the investigation of safety properties in terms
of execution histories, since no interleaving between transactions happen.

Abadi et. al.~\cite{Abadi2011} developed the so-called calculus of automatic mutual exclusion (AME) and
shows how to model the behavior of atomic blocks. Using AME they model STM systems that use
in-place update, optimistic concurrency, lazy-conflict detection and roll-back and determine assumptions
that ensure correctness criteria. As~\cite{Abadi2011}, our work defines
different semantics for the same language with the intent to verify STM algorithms, but they use manual proofs
to assert that their semantics enjoy criteria of interest and our work advocates the use of automated testing
tools to early discover semantic design failures before starting proofs.

Moore et. al.~\cite{Moore2008} proposes a series of languages that model several behaviors of STM. Such
models abstract implementation details and provide high-level definitions. Moore uses small-step operational semantics
to explicitly model interleving execution of threads. Manual proofs of isolation properties are described as a
techinical report~\cite{Moore2008a}.

\paragraph{Safety properties for STM:} Safety criteria for STM was another line of research pursued
recently~\cite{LesaniP14,Guerraoui2008}. Opacity was defined by Guerraoui et. al.~\cite{Guerraoui2008}
and it is described as a condition on generated histories by a TM algorithm and provide a graph-based
characterization of opacity. Such graph is built from histories and an algorithm is considered opaque if
the corresponding graph is acyclic for every possible history. Lesani et. al.~\cite{LesaniP14} describes
an equivalent safety property called markability, which decomposes opacity in three invariants and prove
that these invariants are equivalent to opacity. 


\paragraph{Formal verification of STM:} Formal verification of STM algorithms has been an active subject
of recent research~\cite{Lesani2012,CohenPZ08,cohen2007,Guerraoui2008a,Lesani2013}. Lehsani et.al.~\cite{Lesani2012}
describes a PVS~\cite{Owre1992} formalization of a framework for verifying STM algorithms based on I/O automata. The
main idea of Lehsani's framework is to represent both specifications and algorithms as automata and their equivalence is
verified by proving a simulation relation between these automata. The use of model checker to verify TM algorithms was
the subject of~\cite{CohenPZ08,cohen2007}. Both works use the specification languages of model checkers~\cite{Lamport2002}
to describe STM implementations and check them against safety properties. 
We leave using proof assistants for verifying safety properties of our STM semantics for future work.


\paragraph{Testing algorithms for STM:} Automated testing for a compiler of a STM high-level language to
a virtual machine was the subject of~\cite{Hu08}. He uses QuickCheck to generate random high-level STM
programs and check that their virtual machine compiler preserves the semantics of source programs. Unlike our work that
focus on verifying safety of algorithms expressed as small-step operational semantics, Hu et. al. concerns only with
semantic preservation of compilation process and uses multi-steps to evaluate transactions in a stop-the-world semantics for
their high-level language. While such semantics design choices are reasonable for verifying a semantic preservation theorem for a compiler,
they do allow for checking safety properties. Harmanci et. al.~\cite{Harmanci2009} describes a tool for testing
TM algorithms, called TM-unit. Using TM-unit domain specific language, users can specify TM workloads for both
safety and performance testing of TM algorithms. Authors argue that their domain specific language is simple and
expressive but no formal semantics of this language is provided. We believe that the use of domain specific languages
is invaluable to provide concise and formal specifications of STM algorithm and we leave this line of research for
further work.

\section{Conclusion}\label{sec:conclusion}

In this work we presented safe semantics for a simplied high-level language with STM support and use
property based testing to verify it. The lightweight approach provided by QuickCheck allow us to experiment
with different semantic designs and implementations, and to quickly check any changes. During the development of this work,
we have changed our basic definitions many times, both as a result of correcting errors, and streamlining the presentation.
Ensuring that our changes were consistent was simply a matter of re-running test suite. Encoding safety properties as
Haskell functions over STM histories provides a clean and concise implementation that helps not only to fix semantics
but also to improve our understanding of STM algorithms.

As future work we intend to use Agda~\cite{Norell2009} to provide formally certified proofs that the presented semantics does
enjoy safety properties and also investigate the usage of domain specific languages to ease the task of specifying algorithms
as small-step operational semantics of a simple transactional language.

\bibliographystyle{fundam}
\bibliography{references} 

\end{document}
