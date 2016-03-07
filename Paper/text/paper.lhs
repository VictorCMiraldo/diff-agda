\documentclass[numbers]{sigplanconf}
\usepackage[english]{babel}
\usepackage{savesym}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{wrapfig}
\usepackage{hyperref}
\usepackage{catchfilebetweentags}
\usepackage{agda}
\usepackage[all]{xypic}
\usepackage{tikz}
\usepackage{enumerate}
\usepackage{mathtools}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% WORKFLOW ENVS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newenvironment{TODO}{%
  \color{blue} \itshape \begin{itemize}
}{%
  \end{itemize}
}

\newenvironment{TRASH}{\color{gray} \itshape}{}

\newenvironment{RESEARCH}{%
  \color{magenta} \textbf{To Research!} \itshape \begin{itemize} 
}{%
  \end{itemize}
}

\newcommand{\RESEARCHAnswer}[1]{%
\begin{itemize} \color{red}
  \item \textbf{ANS:} #1
\end{itemize}
}

\newcommand{\warnme}[1]{{\color{red} \textbf{$[$} #1 \textbf{$]$}}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Agda related stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% empty env, maybe later we can add some style to it.
\newenvironment{agdacode}[1][-2em]{%
\vspace{.5em}
\hspace{#1}
\begin{minipage}[t]{.8\textwidth}
}{%
\end{minipage}
\vspace{.5em}
}

\newcommand{\AgdaRaw}[2]{%
\ExecuteMetaData[excerpts/#1.tex]{#2}
}

\newcommand{\AgdaDots}{%
\hskip 3.5em \F{$\vdots$}
}

% Default code, no additional formatting.
\newcommand{\Agda}[2]{%
\begin{agdacode}
\AgdaRaw{#1}{#2}
\end{agdacode}
}

% Allows us to specify how much \hskip we want through #3.
\newcommand{\AgdaI}[3]{%
\begin{agdacode}[#3]
\AgdaRaw{#1}{#2}
\end{agdacode}
}

%% Agda shortcuts
\newcommand{\D}[1]{\AgdaDatatype{#1}}
\newcommand{\F}[1]{\AgdaFunction{#1}}
\newcommand{\K}[1]{\AgdaKeyword{#1}}
\newcommand{\N}[1]{\AgdaSymbol{#1}}
\newcommand{\RF}[1]{\AgdaField{#1}}
\newcommand{\IC}[1]{\AgdaInductiveConstructor{#1}}
\newcommand{\ICArgs}[2]{\AgdaInductiveConstructor{#1}$\; #2 $}
\newcommand{\DArgs}[2]{\D{#1}$\; #2 $}

\newcommand{\textrho}{$\rho$}
\newcommand{\textLambda}{$\Lambda$}
\newcommand{\textpi}{$\pi$}
\renewcommand{\textmu}{$\mu$}
\newcommand{\textsigma}{$\sigma$}
\newcommand{\textSigma}{$\Sigma$}
\newcommand{\texteta}{$\eta$}

% And some others that actually require the unicode declaration
\DeclareUnicodeCharacter {10627}{\{\hspace {-.2em}[}
\DeclareUnicodeCharacter {10628}{]\hspace {-.2em}\}}
\DeclareUnicodeCharacter {8759}{::}
\DeclareUnicodeCharacter {8718}{$\square$}
\DeclareUnicodeCharacter {8799}{$\stackrel{\tiny ? \vspace{-1mm}}{=}$}
\DeclareUnicodeCharacter {8339}{$_x$}
\DeclareUnicodeCharacter {8336}{$_a$}
\DeclareUnicodeCharacter {7523}{$_r$}
\DeclareUnicodeCharacter {7506}{$^\circ$}
\DeclareUnicodeCharacter {8348}{$_t$}
\DeclareUnicodeCharacter {7522}{$_i$}
\DeclareUnicodeCharacter {119924}{$\mathcal{M}$}
\DeclareUnicodeCharacter {8346}{$_p$}
\DeclareUnicodeCharacter {120028}{$\mathcal{M}$}

%%%%%%%%%%%%%%%%%%%%%%%%%%%

% lhs2TeX specifics

%include lhs2TeX.fmt

%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Bibliography 

\newcommand{\mcite}[1]{[FIXBIB]}

%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CSV file formatting

\newcommand{\csvAOBraw}[3]{
\begin{tikzpicture}[sibling distance=4cm, level distance=2cm,
  every node/.style = {shape = rectangle , draw , align=center},
  edge from parent/.style={draw=black,-latex}]
  
  \node {#2}
    child { node {#1} }
    child { node {#3} } ;
\end{tikzpicture}}

\newcommand{\csvAOBlbl}[5]{
\begin{tikzpicture}[sibling distance=4cm, level distance=2cm,
  csv/.style = {shape = rectangle , draw , align=center},
  env/.style = {shape = rectangle , white , draw},
  edge from parent/.style={draw=black,-latex}]
  
  \node [csv] {#2}
    child { node [csv] {#1} edge from parent node [left] {#4} }
    child { node [csv] {#3} edge from parent node [right] {#5} } ;
\end{tikzpicture}}

\newcommand{\csvABlbl}[3]{
\begin{tikzpicture}[sibling distance=4cm, level distance=2cm,
  csv/.style = {shape = rectangle , draw , align=center},
  env/.style = {shape = rectangle , white , draw},
  edge from parent/.style={draw=black,-latex}]
  
  \node [csv] {#1}
    child { node [csv] {#2} edge from parent node [right] {#3} } ;
\end{tikzpicture}}

%%%%%%

\newcommand{\sheltt}[1]{\texttt{\small #1}}

%%%%%%
%% Definitions and lemmas

\newtheorem{definition}{Definition}[section]

%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% LHS formatting rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%

%format BOTP = "\bot_p"
%format BOT  = "\bot"

%%% Domain Specific Typesetting

\newcommand{\Dtty}{\F{D}\;\F{$\bot_p$}\;t\;ty}
\newcommand{\DCtty}{\F{D}\;\F{C}\;t\;ty}
\newcommand{\Patchtty}{\F{Patch}\;t\;ty}
\newcommand{\Ctty}{\F{C}\;t\;ty}

%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Title, etc...
%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}
%\conferenceinfo{ICFP '16}{...}
%\copyrightyear{2016}
%\copyrightdata{...}
%\copyrightdoi{nnnnnn.nnnnnn}
\preprintfooter{some information here...}
\titlebanner{DRAFT}

\title{Structure aware version control}
\subtitle{A case study in Agda}

\authorinfo{Victor Cacciari Miraldo \and Wouter Swierstra}
  {University of Utrecht}
  {\{v.cacciarimiraldo,w.s.swierstra\} at uu.nl}

\maketitle

\begin{abstract}
  The widespread UNIX \texttt{diff3} program is the programmers worst nightmare
for merging non-trivial edits of a given file. The problems with \texttt{diff3}
arise from its unified view over files; all non-binary files are just lines of text.
In the real world, however, we see that most data is much more than just lines of text,
they have a great bunch of structure into it. This paper describes an approach,
generic on the file structure, to obtain and merge changes in a much more elegant way.
We use Agda to prototype and prove properties of our algorithms and Haskell
to implement it. Moreover, we show how our approach scales, allowing programmers
to easily define complex automatic conflict solvers.
\end{abstract}

\category{D.1.1}{Programming Techniques}{Applicative (Functional) Programming}
\category{D.2.7}{Distribution, Maintenance, and Enhancement}{Version control}
\category{D.3.3}{Language Constructs and Features}{Data types and structures}

\terms
Algorithms, Version Control, Agda, Haskell

\keywords
Dependent types, Generic Programming, Edit distance, Patches

%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% THE PAPER
%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{Introduction}


Version control has become an indispensable tool in the development of
modern software. There are various version control tools freely
available, such as git or mercurial, that are used by thousands of
developers worldwide. Collaborative repository hosting websites, such
as GitHub and Bitbucket, haven triggered a huge growth in open source
development. \warnme{Add citations}

Yet all these tools are based on a simple, line-based diff algorithm
to detect and merge changes made by individual developers. While such
line-based diffs generally work well when monitoring small repositories,
with small development teams, they tend to behave sub-optimally in many
real life scenarios. A classical instance is indentation conflicts in source-code
files. This conflicts happen precisely because source-code can be better modeled
using other objects other than lists of lines. 

Consider the following example CSV file, recording the marks and names
three students:

\begin{center}
\begin{tabular}{l@@{ , }l@@{ , }l}
Name & Number & Mark \\
Alice & 440 & 7.0 \\
Bob & 593 & 6.5 \\
Carroll & 168 & 8.5
\end{tabular}
\end{center}


Adding a new line to this CSV file will not modify any existing entries and
is unlikely to cause conflicts. Adding a new column storing the date
of the exam, however, will change every line of the file and therefore
will conflict with any other change to the file. Conceptually,
however, this seems wrong: adding a column changes every line in the
file, but leaves all the existing data unmodified. The only reason
that this causes conflicts is that the \emph{granularity of change}
that version control tools use is not suitable for this kind of file.

This paper proposes a different approach to version control
systems. Instead of relying on a single line-based diff algorithm, we
will explore how to define a \emph{generic} notion of change, together
with algorithms for observing and combining such changes. To this end,
this paper makes the following novel contributions:
  
\begin{itemize}
  \item We define a universe representation for data and a 
        \emph{type-indexed} data type for representing edits to this
        structured data. The structure of the data closely resembles the way
        one defines datatypes in functional languages such as Haskell.

  \item We define generic algorithms for computing and applying a diff
        generically and prove they are correct with respect to each other.


  \item A notion of residual is used to propagate changes of different diffs,
        hence providing a bare mechanism for merging and conflict resolution.

  \item We illustrate how these ideas in Agda\cite{norell2009} have been implemented in a
        prototype Haskell tool, capable of automatically merging changes to
        structured data. This tool provides the user with the ability to define
        custom conflict resolution strategies when merging changes to structured
        data. For instance, we can automatically resolve refactoring conflicts.
\end{itemize}    

\subsection*{Background}

  The generic diff problem is a very special case of the \emph{edit distance} problem,
which is concerned with computing the minimum cost of transforming an untyped tree 
$A$ into an untyped tree $B$. Demaine provides a solution to the problem in 
\cite{Demaine2007}, improving the work of \cite{Klein1998}. This problem
has been popularized in the particular case where the trees in question are,
in fact, lists, in which case we call it the \emph{least common subsequence} (LCS)
problem \cite{Bille2005,Bergroth2000}. The popular UNIX \texttt{diff} tool provides
a solution to the LCS problem considering the edit operations to be inserting and 
deleting lines of text.

  Our implementation follows a slightly different route, in which we choose
not to worry too much about the \emph{minimum} cost, but the one that better reflects
the changes which are important to the use case in question. In practice, we can see
that the \emph{diff} tool works great. Its problem is precisely conflict resolution,
or more generally, its older brother \emph{diff3} \cite{Khanna2007}. Conflict resolution
is where our focus lies. We want to build a sound theory for patches that is highly customizable 
in its conflict solving capabilities, as it can be used for arbitrarily many file formats.
In order to build such theory, and consequently a prototype, we will turn ourselves to
datatype-generic programming, where functional programming technology excels at.
  
\section{Structural Diffing}  
  
  To make version control to be structure aware we need to define what
structures we can handle. In our case, the structure is the universe of context
free types, patching will be defined for its inhabitants.
  
\newcommand{\CF}{\text{CF}}
\subsection{Context Free Datatypes}
\label{sec:cf}

  The universe of \emph{context-free types}, in the sense of
\cite{Altenkirch2006}, is constructed following the grammar $\CF$ of
context free types with a deBruijn representation for variables, figure \ref{fig:cfgrammar}.
  
  \begin{figure}[h]
  \[
    \CF ::= 1 \mid 0 \mid \CF \times \CF \mid \CF + \CF \mid \mu \; \CF \mid \mathbb{N}
              \mid (\CF \; \CF)
  \]
  \caption{BNF for $\CF$ terms}
  \label{fig:cfgrammar}
  \end{figure}
  
  In Agda, the $\CF$ universe is defined by:
  
  \Agda{Diffing/Universe/Syntax}{U-def}
  
  In order to make life easier we use a deBruijn indexing for our type variables.
an element of $\F{U}\;n$ reads as a type with $n$ free type variables. \IC{$u0$}
and \IC{$u1$} represent the empty type and unit, respectively. Products
and coproducts are represented by \IC{$\_\otimes\_$} and \IC{$\_\oplus\_$}. 
Recursive types are created through \IC{$\mu$}. Type application is 
denoted by \IC{$\beta$}. To control and select variables we use constructors
that retrieve the \emph{top} of the variable stack, \IC{$vl$}, and that
\emph{pop} the variable stack, ignoring the top-most variable, \IC{$wk$}.
We could have used a \F{Fin} to identify variables, and have one instead of 
two constructors for variables, but that would trigger more complicated 
definitions later on.
  
  Stating the language of our types is not enough. We need to specify its
elements too, after all, they are the domain which we seek to define our
algorithms for! Defining elements of fixed-point types make things a bit more
complicated, check \cite{Altenkirch2006} for a more in-depth explanation of
these details. We need a decreasing \F{Tel}escope of types in order to specify
the elements of \F{U} and still pass the termination checker. The reason for
having this telescope is simple. Imagine we want to describe the 
elements of a type with $n$ variables, $ty : \F{U}\;n$. We can only speak about
this type once all $n$ variables are bound to correspond to a given type. 
We need then $t_1, t_2, \cdots, t_n$ to pass as \emph{arguments} to $ty$. 
Moreover, these types have to have less free variables then $ty$ itself,
otherwise this will never finish. This list of types with decreasing
type variables is defined through \F{Tel}:

  \Agda{Diffing/Universe/Syntax}{Tel-def}

 A value $(v\; :\; \F{ElU}\; \{n\}\; ty\; t)$ reads roughly
as: a value of type $ty$ with $n$ variables, applied to telescope $t$. 
At this point we can define the actual $v$'s that inhabit every code
in $\F{U}\;n$.  In Agda, the elements of \F{U} are defined by:
  
  \Agda{Diffing/Universe/Syntax}{ElU-def}
  
  The set \F{ElU} of the elements of \F{U} is straight forward. We begin with some simple
constructors to handle finite types: \IC{void}, \IC{inl}, \IC{inr} and \IC{$\_,\_$}.
Next, we define how to reference variables using \IC{pop} and \IC{top}. Finally,
\IC{mu} and \IC{red} specify how to handle recursive types and type applications.
  
  Let us see a simple example of how types and elements are defined in this
framework. Consider that we want to encode the list |(u : []) :: [U]|, for
|U| being the unit type with the single constructor |u|. We start by defining
the type of lists, this is an element of $\F{U}\;(\IC{suc}\;n)$, which later
lets us define an element of that type.

  \Agda{Diffing/Universe/Syntax}{U-example}
  
  Up until now we showed how to define the universe of context free types
and the elements that inhabit it. We are, however, interested in the operations
can we perform on these elements. As we shall see, this choice of universe
turns out to be very expressive, providing a plethora of interesting operations that
can be defined by induction on \F{U}.
The first very useful concept is the decidability of generic 
equality\cite{Altenkirch2006}.

  \Agda{Diffing/Universe/Equality}{equality-type}
  
  But only comparing things will not get us very far. We need to be able to
inspect our elements generically. A very natural way to do so is to see an element 
of a given type as a tree. We can define operations like getting the list of immediate children,
or computing their arity, that is, how many children do they have. Such operations,
coupled with generic decidable equality, allows us to traverse and compare two arbitrary
trees.

  \Agda{Diffing/Universe/Ops}{children-type}
  
  \Agda{Diffing/Universe/Ops}{arity-type}
  
  The advantage of doing so in Agda, is that we can prove that our definitions 
are correct.
  
  \Agda{Diffing/Universe/Ops}{children-arity-lemma-type}
  
  Intuitively, the list of children of an element $\F{ElU}\;ty\;(\IC{tcons}\;a\;t)$
contains one $\F{ElU}\;a\;t$ for every occurrence of $\IC{vl}$ in $ty$.  
  We can even go a step further and say that every element is defined by a constructor
and a vector of children, with the correct arity. This lets us treat generic elements as
elements of a (typed) rose-tree, whenever that is convenient.

  \Agda{Diffing/Universe/Ops}{unplug-type}
  
  \Agda{Diffing/Universe/Ops}{plug-type}
  
  \Agda{Diffing/Universe/Ops}{plug-correct-type}
  
  These operations are central to solving the diffing problem, for we need
a way of traversing generic trees in order to decide how to change one into the other.
We do things a bit differently, though. We linearize the trees and proceed to traverse
the resulting list.

  For the readers familiar with Haskell's \emph{Uniplate}\cite{Mitchell2008} library,
our \F{plug} and \F{unplug} operations allow for a similar view over datatypes.
For instance, we can define the \F{transform} function in Agda as: 

  \Agda{Diffing/Universe/Lab}{transform-type}
  
  Note that we first need to pattern-match on the telescope, as types with
zero variables can not be \emph{unplugged}. 
  
  This repertoire of operations, and the ability to inspect an element structurally,
according to its type, gives us the tool set we need in order to start describing
differences between elements. That is, we can now start discussing what does it mean
to \emph{diff} two elements or \emph{patch} an element according to some description
of changes.  
  
\subsection{Patches over a Context Free Type}

  The type of \emph{diff}'s is defined by \F{D}. It is indexed by a type
and a telescope, which is the same as saying that we only define \emph{diff}'s for
closed types\footnote{Types that do not have any free type-variables}. However,
it also has a parameter $A$, this will be addressed later.

  \Agda{Diffing/Patches/Diff/D}{D-type}
  
  As we mentioned earlier, we are interested in analyzing the set of possible
changes that can be made to objects of a type $T$. These changes depend on
the structure of $T$, for the definition follows by induction on it.

  If $T$ is the Unit type, we can not modify it.

  \Agda{Diffing/Patches/Diff/D}{D-void-def}
  
  If $T$ is a product, we need to provide \emph{diffs} for both
its components.

  \Agda{Diffing/Patches/Diff/D}{D-pair-def}
  
  If $T$ is a coproduct, things become slightly more interesting. There
are four possible ways of modifying a coproduct, which are defined by:

  \Agda{Diffing/Patches/Diff/D}{D-sum-def}
  
  Let us take a closer look at the diffs of a coproduct. There are four possibilities
when modifying a coproduct $a\;\IC{$\oplus$}\;b$. Given some 
diff $p$ over $a$, we can always modify things that inhabit the left
of the coproduct by $\IC{D-inl}\; p$. Or we can change some given value
$\IC{left}\;x$ into a $\IC{right}\;y$, this is captured by $\IC{D-setl}\;x\;y$.
The case for \IC{D-inr} and \IC{D-setr} are analogous.
  
  We also need some housekeeping definitions to make sure we handle all
types defined by \F{U}.

  \Agda{Diffing/Patches/Diff/D}{D-rest-def}
  
  Fixed points are handled by a list of \emph{edit operations}. We will
discuss them in detail later on.

  \Agda{Diffing/Patches/Diff/D}{D-mu-def}
  
  The aforementioned parameter $A$ is used in a single constructor,
allowing us to have a free-monad structure over \F{D}'s. This technique shows to be
very useful for adding extra information, as we shall discuss, on section 
\ref{sec:conflicts}, for adding conflicts.

  \Agda{Diffing/Patches/Diff/D}{D-A-def} 
  
  If \F{D} is a free-monad it is also, in particular, a functor. For we
have the equivalent mapping of a function on a \F{D}-structure, denoted by $\F{D-map}$.
Moreover, we can also ignore the \F{D}-structure and fetch only the $A$'s inside,
we call this $\F{forget}\; : \: \forall A\;t\;ty \; . \; \F{D}\;A\;t\;ty \rightarrow \F{List}\;A$.
It is worth mentioning that all the indexes involved make the actual Agda type
much more complicated. The intuition and the functionality stays the same, however.
  Finally, we define $\Patchtty$ as $\F{D}\;(\lambda \;\_\;\_ \rightarrow \bot)\; t\; ty$.
Meaning that a \F{Patch} is a \F{D} with \emph{no} extra information.

\subsection{Producing Patches}  
  
  Given a generic definition of possible changes, the primary goal is to produce
an instance of this possible changes, for two specific elements of a type $T$.
We shall call this process \emph{diffing}. It is important to note that
our \F{gdiff} function expects two elements of the same type! This contrasts
with the work done by Vassena\cite{Vassena2015} and Lempsink\cite{Loh2009}, where
their diff takes objects of two different types. 
  
  For types which are not fixed points, the \F{gdiff} functions follows the 
structure of the type:
  
  \Agda{Diffing/Patches/Diff}{gdiff-def}
  
  Where the \F{gdiffL} takes care of handling fixed point values. The important
remark here is that it operates over lists of elements, instead of single
elements. This is due to the fact that the children of a fixed point element
is a (possibly empty) list of fixed point elements. 

\paragraph{Recursion}

  Fixed-point types have a fundamental difference over the other type
constructors in our universe. They can grow or shrink arbitrarily. We have to
account for that when tracking differences between their elements. As we
mentioned earlier, the diff of a fixed point is defined by a list of \emph{edit
operations}.
  
  \Agda{Diffing/Patches/Diff/D}{Dmu-type}
  
  But the interesting bits are the \emph{edit operations} we allow.
We define $\F{Val}\;a\;t = \F{ElU}\;a\;(\IC{tcons}\;\IC{u1}\;t)$ as the 
elements of type $a$ where the recursive occurrences of \IC{$\mu$ }$a$ are erased.
  
  \Agda{Diffing/Patches/Diff/D}{Dmu-def}
  
  Again, we have a constructor for adding \emph{extra} information, which is
ignored in the case of \F{Patches}.

  \Agda{Diffing/Patches/Diff/D}{Dmu-A-def}
  
  The edit operations we allow are very simple. We can add or remove parts
of a fixed-point or we can modify non-recursive parts of it.
and instead of copying, we introduce a new constructor, \IC{D$\mu$-dwn}, which
is responsible for traversing down the type-structure. Copying is modeled by
$\IC{D$\mu$-dwn}\;(\F{gdiff}\; x \; x)$. The intuition is that for every object
$x$ there is a diff that does not change $x$, we will look into this on
section \ref{sec:id}.
  
  Before we delve into diffing fixed point values, we need some specialization
of our generic operations for fixed points. Given that $\mu X . F\; X \approx
F\;1 \times \F{List}\;(\mu X . F\; X)$, that is, any inhabitant of a fixed-point type can
be seen as a non-recursive head and a list of recursive children. We then make
a specialized version of the \F{plug} and \F{unplug} functions, which lets us
open and close fixed point values.
  
  \Agda{Diffing/Universe/MuUtils}{Openmu-def}
  
  \Agda{Diffing/Universe/MuUtils}{mu-open-type}
  
  \Agda{Diffing/Universe/MuUtils}{mu-close-type}
  
  Although the \F{plug} and \F{unplug} uses vectors,
here we switch to lists instead, this way we can easily
construct a fixed-point with the beginning of the list of children, and return
the unused children. The only reason being convenience when defining how patches are applied. 
Nevertheless, a soundness lemma guarantees the correct behavior.
  
  \Agda{Diffing/Universe/MuUtils}{mu-close-resp-arity-lemma}
  
  We denote the first component of an \emph{opened} fixed point by its
\emph{value}, or \emph{head}; whereas the second component by its children. These
lemmas suggest that we handle fixed points in a serialized fashion. Since we never
really know how many children will need to be handled in each step, we make \F{gdiffL}
handle lists of elements or, forests, since every element is in fact a tree.
Our algorithm, which was heavily inspired by \cite{Loh2009}, is then
defined by:
  
  \Agda{Diffing/Patches/Diff}{gdiffL-def}  
  
\newcommand{\lubmu}{\sqcup_{\mu} \;}
\newcommand{\Flubmu}{\; \F{$\lubmu$} \;}
  The first three branches are simple. To transform |[]| into |[]|, we do not
need to perform any action; to transform |[]| into |y : ys|, we need to insert
the respective head and add the children to the \emph{forest}; and to transform
|x : xs| into |[]| we need to delete the respective values. The interesting case
happens when we want to transform |x:xs| into |y:ys|. Here we have three
possible diffs that perform the required transformation. We want to choose the
diff with the least \emph{cost}, for we introduce an operator to do exactly
that:

  \Agda{Diffing/Patches/Diff/Cost}{lubmu-def}

  As we shall see in section \ref{sec:cost}, this notion of cost is very
delicate. The idea, however, is simple. If the heads are equal we have $d3 =
\IC{D$\mu$-dwn}\; (\F{gdiff}\; hdX\; hdX) \cdots$, which is how the copying
instruction is encoded. It is clear that we want to copy as much as possible, so
we will ensure that for all $a$, $\F{gdiff}\;a\;a$ has cost 0 whereas
\IC{D$\mu$-ins} and \IC{D$\mu$-del} will have strictly positive cost. Therefore,
we want to use the cost of a diff to drive the algorithm.

  Note, however, that $\F{gdiff}\;a\;a$ is the patch that changes $a$ into $a$.
Well, but there are no changes to be made whatsoever. As it turns out, we do
have some special patches that deserve some attention. They are the
\emph{identity patch} and the \emph{inverse patch}. As we shall see later, the
intuition from these two special patches will greatly influence how \F{cost} is
defined.

\paragraph*{The Identity Patch}
\label{sec:id}

  Given the definition of \F{gdiff}, it is not hard to see that whenever
$x \equiv y$, we produce a patch without any \IC{D-setl}, \IC{D-setr},
\IC{D$\mu$-ins} or \IC{D$\mu$-del}, as they are the only constructors of \F{D} that
introduce \emph{new information}. Hence we call these the \emph{change-introduction} constructors. 
One can then spare the comparisons made by \F{gdiff} and trivially define the
identity patch for an object $x$, $\F{gdiff-id}\; x$, by induction on $x$. A
good sanity check, however, is to prove that this intuition is in fact correct:
  
  \Agda{Diffing/Patches/Diff/Id}{gdiff-id-correct-type}
  
  Later on we will talk about applying patches, for we will see that this is
in fact the identity for $x$ in \emph{patch-space}.
  
\paragraph*{The Inverse Patch} 

  If a patch $\F{gdiff}\;x\;y$ is not the identity, then it has \emph{change-introduction} constructors.
if we swap every \IC{D-setl} for \IC{D-setr}, and \IC{D$\mu$-ins} for \IC{D$\mu$-del} and
vice-versa, we get a patch that transforms $y$ into $x$. We shall call this operation the inverse
of a patch.

  \Agda{Diffing/Patches/Diff/Inverse}{D-inv-type}
  
  As one would expect, $\F{gdiff}\;y\;x$ or $\F{D-inv}\;(\F{gdiff}\;x\;y)$
should be the same patch. In fact, we have that $\F{gdiff}\;y\;x \approx \F{D-inv}\;(\F{gdiff}\;x\;y)$.
That is to say $\F{gdiff}\;y\;x$ is \emph{observationally} the same as $\F{D-inv}\;(\F{gdiff}\;x\;y)$,
but may not be identical. In the presence of equal cost alternatives they may make
different choices.
  
\subsubsection{The Cost Function}
\label{sec:cost}
  
  As we mentioned earlier, the cost function is one of the key pieces of the
diff algorithm. It should assign a natural number to patches.

  \Agda{Diffing/Patches/Diff/Cost}{cost-type}

The question is, how should we do this? The cost of transforming $x$ and $y$
intuitively leads one to think about \emph{how far is $x$ from $y$}. We see that
the cost of a patch should not be too different from the notion of distance.

\[  \F{dist}\;x\;y = \F{cost}\;(\F{gdiff}\;x\;y) \]

  \vskip .5em

  In order to achieve a meaningful definition, we will impose the specification
that our \F{cost} function must make the distance we defined above into a metric.
We then proceed to calculate the \F{cost} function from its specification. Remember
that we call a function \emph{dist} a \emph{metric} iff:
  
  \vskip -1em
  \begin{eqnarray}
    dist\;x\;y = 0 & \Leftrightarrow & x = y \\
    dist\;x\;y & = & dist\;y\;x \\
    dist\;x\;y + dist\;y\;z & \geq & dist\;x\;z
  \end{eqnarray}

  Equation (1) tells that the cost of not changing anything must be 0, therefore
the cost of every non-\emph{change-introduction} constructor should be 0. The
identity patch then has cost 0 by construction, as we seen it is exactly the patch
with no \emph{change-introduction} constructor.

  Equation (2), on the other hand, tells that it should not matter whether we go
from $x$ to $y$ or from $y$ to $x$, the effort is the same. In patch-space, this
means that the inverse of a patch should preserve its cost. Well, the inverse
operation leaves everything unchanged but flips the \emph{change-introduction}
constructors to their dual counterpart. We will hence assign a cost $c_\oplus =
\F{cost } \IC{D-setl} = \F{cost } \IC{D-setr}$ and $c_\mu = \F{cost }
\IC{D$\mu$-ins} = \F{cost } \IC{D$\mu$-del}$ and guarantee this by construction
already. 
  Some care must be taken however, as if we define $c_\mu$ and $c_\oplus$ as constants
we will say that inserting a tiny object has the same cost of inserting a gigantic object!
That is not what we are looking for in a fine-tuned diff algorithm. Let us then define
$c_\oplus\;x\;y = \F{cost }(\IC{D-setr}\;x\;y) = \F{cost }(\IC{D-setl}\;x\;y)$ and
$c_\mu\;x = \F{cost }(\IC{D$\mu$-ins}\;x) = \F{cost }(\IC{D$\mu$-del}\;x)$ so we can
take this fine-tuning into account.

  Equation (3) is concerned with composition of patches. The aggregate cost of changing
$x$ to $y$, and then $y$ to $z$ should be greater than or equal to changing
$x$ directly to $z$. We do not have a composition operation over patches yet, but
we can see that this is already trivially satisfied. Let us denote the number of 
\emph{change-introduction} constructors in a patch $p$ by $\# p$. In the best case scenario,
$\# (\F{gdiff}\;x\;y) + \# (\F{gdiff}\;y\;z) = \# (\F{gdiff}\;x\;z)$, this is the situation
in which the changes of $x$ to $y$ and from $y$ to $z$ are non-overlapping. If they
are overlapping, then some changes made from $x$ to $y$ must be changed again from $y$ to $z$,
yielding $\# (\F{gdiff}\;x\;y) + \# (\F{gdiff}\;y\;z) > \# (\F{gdiff}\;x\;z)$. 

  \vskip .3em

  From equations (1) and (2) and from our definition of the identity patch and
the inverse of a patch we already have that:

  \Agda{Diffing/Patches/Diff/Id}{gdiff-id-cost-type}
  
  \Agda{Diffing/Patches/Diff/Inverse}{D-inv-cost-type}
  
  In order to finalize our definition, we just need to find an actual value for
$c_\oplus$ and $c_\mu$. We have a lot of freedom to choose these values, however,
yet, they are a critical part of the diff algorithm, since they will drive it to prefer some
changes over others. 

  We will now calculate a relation that $c_\mu$ and $c_\oplus$ need to satisfy
for the diff algorithm to weight changes in a top-down manner. That is, we want
the changes made to the outermost structure to be \emph{more expensive} than the
changes made to the innermost parts.

  Let us then take a look at where the difference between $c_\mu$ and $c_\oplus$ comes
into play, and calculate from there. Assume we have stopped execution of
\F{gdiffL} at the $d_1 \Flubmu d_2 \Flubmu d_3$ expression. Here we have three
patches, that perform the same changes in different ways, and we have to choose
one of them.

\newcommand{\cons}{\; :\hskip -.1em : \;}
\newcommand{\cat}{\; + \hskip -.8em + \;}
\newcommand{\DmuIns}{\IC{D$\mu$-ins} \;}
\newcommand{\DmuDel}{\IC{D$\mu$-del} \;}
\newcommand{\DmuDwn}{\IC{D$\mu$-dwn} \;}
\newcommand{\ICoplus}{\; \IC{$\oplus$} \;}
\begin{center}
\vskip -1em
\[
\begin{array}{l c l}  
  d_1 & = & \DmuIns hdY \cons \F{gdiffL}\;(x \cons xs)\;(chY \cat ys) \\
  d_2 & = & \DmuDel hdX \cons \F{gdiffL}\;(chX \cat xs)\;(y \cons ys) \\
  d_3 & = & \DmuDwn (\F{gdiff}\;hdX\;hdY) \\ 
      & \cons & \F{gdiffL}\;(chX \cat xs)\;(chY \cat ys)
\end{array}
\]
\end{center}

  We will only compare $d_1$ and $d_3$, as the cost of
inserting and deleting should be the same, the analysis for $d_2$ is analogous.
By choosing $d_1$, we would be opting to insert $hdY$ instead of transforming
$hdX$ into $hdY$, this is preferable only when we do not have to delete $hdX$
later on, in $\F{gdiffL}\;(x \cons xs)\;(chY \cat ys)$, as that would be a waste
of information. Deleting $hdX$ is inevitable when $hdX \notin chY \cat ys$. 
Assuming without loss of generality that this deletion happens in the next
step, we have:

\begin{eqnarray*}
  d_1 & = & \DmuIns hdY \cons \F{gdiffL}\;(x \cons xs)\;(chY \cat ys) \\
      & = & \DmuIns hdY \cons \F{gdiffL}\;(hdX \cons chX \cat xs)\;(chY \cat ys) \\
      & = & \DmuIns hdY \cons \DmuDel hdX \\
      & & \hskip 1.72cm \cons \F{gdiffL}\;(chX \cat xs)\;(chY \cat ys) \\
      & = & \DmuIns hdY \cons \DmuDel hdX \cons \F{tail }d_3
\end{eqnarray*}

  Hence, \F{cost }$d_1$ is $c_\mu\;hdX + c_\mu\;hdY + w$, for $w =
\F{cost}\;(\F{tail}\;d_3)$. Obviously, $hdX$ and $hdY$ are values of the same
type. Namely $hdX , hdY : \F{ElU}\;ty\;(\IC{tcons}\;\IC{u1}\;t)$. Since we want
to apply this to Haskell datatypes by the end of the day, it is acceptable to
assume that $ty$ is a coproduct of constructors. Hence $hdX$ and $hdY$ are
values of the same finitary coproduct, representing the constructors of the
fixed-point datatype. If $hdX$ and $hdY$ comes from different constructors,
then\footnote{
%%%% FOOTNOTE
We use $i_j$ to denote the $j$-th injection into a finitary coproduct. 
%%%% FOOTNOTE
} $hdX = i_j\; x'$ and $hdY = i_k\; y'$ where $j \neq k$. The patch from $hdX$
to $hdY$ will therefore involve a $\IC{D-setl}\;x'\;y'$ or a
$\IC{D-setr}\;y'\;x'$, hence the cost of $d_3$ becomes $c_\oplus\;x'\;y' + w$.
Remember that we are still in the situation where it is wise to delete and
insert instead of recursively changing. The reasoning behind it is simple: since
things are coming from a different constructors the structure of the outermost
type is definitely changing, we want to reflect that! This means we need to
select $d_1$ instead of $d_3$, that is, we need to attribute a cost to $d_1$
that is strictly lower than the cost of $d_3$:

\[
\begin{array}{crcl}
  & c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y') + w & < & c_\oplus\;(i_j\;x')\;(i_k\;y') + w \\
  \Leftrightarrow & c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y') & < & c_\oplus\;(i_j\;x')\;(i_k\;y')
\end{array}
\]

  If $hdX$ and $hdY$ come from the same constructor, on the other hand, the
story is slightly different. We now have $hdX = i_j\;x'$ and $hdY = i_j\;y'$,
the cost of $d_1$ still is $c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y') + w$ but the
cost of $d_3$ is $\F{dist}\;x'\;y' + w$, since $\F{gdiff}\;hdX\;hdY$ will be
$\F{gdiff}\;x'\;y'$ preceded by a sequence of \IC{D-inr} and \IC{D-inr}, for
$hdX$ and $hdY$ they come from the same coproduct injection, and these have cost
0. This is the situation that selecting $d_3$ is the best option, therefore we
need:

\[
\begin{array}{crcl}
  & \F{dist}\;x'\;y' + w & < & c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y') + w \\
  \Leftrightarrow & \F{dist}\;x'\;y' & < & c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y')
\end{array}
\]

In order to enforce this behavior on our diffing algorithm, we need to assign
values to $c_\mu$ and $c_\oplus$ that respects:

\[ \F{dist}\;x'\;y' < c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y') < c_\oplus\;(i_j\;x')\;(i_k\;y') \]

  Note that there are an infinite amount of definitions that would fit here.
This is indeed a central topic of future work, as the \F{cost} function is what
drives the diffing algorithm. So far we have calculated a relation between
$c_\mu$ and $c_\oplus$ that will make the diff algorithm match in a top-down
manner. That is, changes to the outermost type are seen as the heaviest changes.
Different domains may require different relations. For a first generic
implementation, however, this relation does make sense. Now is the time for
finally assigning values to $c_\mu$ and $c_\oplus$ and the diffing algorithm is
completed. We simply define the cost function in such a way that it has to
satisfy the imposed constraints.

  \Agda{Diffing/Patches/Diff/Cost}{cost-def}
  
  Where $\F{costL} = sum \cdot map\; \F{cost$\mu$}$ and the size of an element
is defined by:
  
  \Agda{Diffing/Universe/Measures}{sizeEl}

\subsection{A Small Example}

  Let us consider a simple edit to a file containing students name, number and
grade, as in figure \ref{fig:samplepatch}. Assume that John, the responsible for
the grades now knows that Carroll did drop out and that there was a mistake in
Alice's grade. He then proceeds to edit the CSV file in order to reflect these
changes.

\begin{figure}[h]
\begin{center}
\csvABlbl{\begin{tabular}{l@@{ , }l@@{ , }l}
Name & Number & Mark \\
Alice & 440 & 7.0 \\
Bob & 593 & 6.5 \\
Carroll & 168 & 8.5
\end{tabular}}{\begin{tabular}{l@@{ , }l@@{ , }l}
Name & Number & Mark \\
Alice & 440 & 8.0 \\
Bob & 593 & 6.5
\end{tabular}}{$p_{John}$}
\end{center}
\caption{Sample Patch}
\label{fig:samplepatch}
\end{figure}

  For readability purposes, we will omit the boilerplate \F{Patch} constructors.
When diffing both versions of the CSV file, we get the patch that reflect John's
changes over the initial file. Remember that $(\DmuDwn (\F{gdiff-id}\;a))$ is
merely copying $a$. The CSV structure is easily definable in \F{U} as $CSV =
\IC{$\beta$}\; \F{list}\; (\IC{$\beta$}\; \F{list}\; X)$, for some appropriate atomic
type $X$ 

\begin{eqnarray*}
  p_{John} & = & \DmuDwn \; (\F{gdiff-id} \; "Name , ...") \\
           & \cons & \begin{array}{r l}
                      \DmuDwn ( & \DmuDwn \; (\F{gdiff-id}\;Alice) \\
                      \cons   & \DmuDwn \; (\F{gdiff-id}\; 440) \\
                      \cons   & \DmuDwn \; (\F{gdiff}\;7.0\;8.0) \\
                      \cons & \DmuDwn (\F{gdiff-id} {[} {]}) \\
                      {[}  {]}      & )
                    \end{array} \\
           & \cons & \DmuDwn \; (\F{gdiff-id}\; "Bob , ...") \\
           & \cons & \DmuDel \; "Carroll, ..." \\
           & \cons & \DmuDwn (\F{gdiff-id} {[} {]}) \\
           & {[} {]} &
\end{eqnarray*}

  Note how the patch closely follow the structure of the changes. There is a
single change, which happens at \emph{Alice's mark} and a single deletion. Note
also that we have to copy the end of both the inner and outer lists, this should
not be confused with the list of edit operations.

\subsection{Applying Patches}
\label{sec:apply}

  At this stage we are able to: work generically on a suitable universe; describe
how elements of this universe can change and compute those changes. In order to
make our framework useful, though, we need to be able to apply the patches we
compute. The application of patches is easy, thus we only
show the implementation for coproducts and fixed points here. The rest is very
straightforward.

  Patch application is a partial operation, however. A patch over $T$ is an object that
describe possible changes that can be made to objects of type $T$. The
high-level idea is that diffing two objects $t_1 , t_2 : T$ will produce a patch
over $T$, whereas applying a patch over $T$ to an object will produce a
$Maybe\;T$. It is interesting to note that application can not be made total.
Let's consider $T = X + Y$, and now consider a patch $(Left\; x) \xrightarrow{p}
(Left\; x')$. What should be the result of applying $p$ to a $(Right\; y)$? It
is undefined!

  \begin{agdacode}
  \AgdaRaw{Diffing/Patches/Diff}{gapply-type}
  \AgdaRaw{Diffing/Patches/Diff}{gapply-sum-def}
  \AgdaRaw{Diffing/Patches/Diff}{gapply-mu-def}
  \AgdaDots
  \end{agdacode}
  
  \Agda{Diffing/Patches/Diff}{gapplyL-def}
  
  Where \F{<\$>} is the applicative-style application for the \emph{Maybe} monad;
\RF{>>=} is the usual bind for the \emph{Maybe} monad and \F{safeHead} is the 
partial head function with type |[a] -> Maybe a|. In \F{gapplyL}, we have
a \F{gIns} function, which will get a value and a list of children of a
fixed point, will try to \F{$\mu$-close} it and add the result to the
head of the remaining list. On the other hand, \F{gDel} will \F{$\mu$-open}
the head of the received list and compare its value with the received value,
if they are equal it returns the tail of the input list appended to its children,
if they are not equal it returns \IC{nothing}.

  Instead of presenting an example, lets provide some intuition for our \F{gapply} function.
Looking at the \IC{D-setl} case, for instance. $\F{gapply}\;(\IC{D-setl}\;x\;y)$ is expecting
to transform a $\IC{inl}\; x$ into a $\IC{inr}\;y$. Upon receiving a
\IC{inl} value, we need to check whether or not its contents are equal to $x$.
If they are, we are good to go. If not, we have to return nothing as we cannot possibly
know what to do. If we look instead on the $\IC{D-inl}\;diff$ branch, we see that
it only succeeds upon receiving a $\IC{inl}\;x$, given that $\F{gapply}\;diff$ succeeds in
modifying $x$.

  The important part of application, nevertheless, is that it must produce the 
expected result. A correctness result guarantees that. Its
proof is too big to be shown here but it has type:

  \Agda{Diffing/Postulated}{gdiff-correctness}
  
  Combining \F{correctness} and $\F{gdiff-id}\;a \equiv \F{gdiff}\;a\;a$ lemma,
by transitivity, we see that our identity patch is in fact the identity. The
\emph{observational} equality of a patch and its inverse is obtained by
transitivity with \F{correctness} and the following lemma:
  
  \Agda{Diffing/Patches/Diff/Inverse}{D-inv-sound-type}
  
  We have given algorithms for computing and applying differences over
elements of a generic datatype. Moreover, we proved our algorithms are correct
with respect to each other. This functionality is necessary for constructing
a version control system, but it is by no means sufficient!
   
\section{Patch Propagation}
\label{sec:residual}

  In a nutshell, any version control system must accomplish two tasks: (A) we
need to be able to produce and apply patches and (B) we need to be able to merge
different, concurrent, changes made to the same object. We have taken care of
task (A) in the previous sections, and even though current VCS tools already
excel at obtaining patches, there is a big lack of tools excelling at (B), that
is, merging patches. All the structural information we are using in task (A) is,
in fact, providing a lot more to help us at task (B), as we shall discuss in
this section.

  The task of merging changes arise when we have multiple users changing the
same file at the same time. Imagine Bob and Alice perform concurrent edits in an
object $A_0$, which are captured by patches $p$ and $q$. The center of the
repository needs to keep only one copy of that object, but upon receiving the
changes of both Bob and Alice we have:

  \[ \xymatrix{ A_1 & A_0 \ar[l]_{p} \ar[r]^{q} & A_2} \]

  Our idea, inspired by \cite{Tieleman2006}, is to incorporate the changes
expressed by $p$ into a new patch, namely one that is aimed at being applied
somewhere already changed by $q$, and vice-versa, in such a way that they
converge. We call this the residual patch. The diagram in figure
\ref{fig:residual} illustrates the result of merging $p$ and $q$ through
propagation.
  
  \begin{figure}[h]
  \begin{displaymath}
    \xymatrix{
         & A_0 \ar[dl]_{p} \ar[dr]^{q} &  \\
         A_1 \ar[dr]_{q / p} & & A_2 \ar[dl]^{p / q} \\
         & A_3 &     
      }
  \end{displaymath}
  \caption{Residual patch square}
  \label{fig:residual}
  \end{figure}
    
  The residual $p / q$ of two patches $p$ and $q$ captures the
notion of incorporating the changes made by $p$ in an object that has already
been modified by $q$. 

  In an ideal world, we would expect the residual function to have type
$\F{Patch}\;t\;ty \rightarrow \F{Patch}\;t\;ty \rightarrow \F{Patch}\;t\;ty$.
Real life is more complicated. To begin with, it only makes sense to compute the
residual of patches that are \emph{aligned}, that is, they can be applied to the
same input. For this, we make the residual function partial though the |Maybe|
monad: $\F{Patch}\;t\;ty \rightarrow \F{Patch}\;t\;ty \rightarrow
\F{Maybe}\;(\F{Patch}\;t\;ty)$ and define two patches to be aligned if and only
if their residual returns a \IC{just}.
  
  Partiality solves just a few problems, what if, for instance, Bob and Alice
changes the same cell in their CSV file? Then it is obvious that someone (human)
have to chose which value to use in the final, merged, version. 
  
  For this illustration, we will consider the conflicts that can arise from
propagating the changes Alice made over the changes already made by Bob, that
is, $p_{Alice} / p_{Bob}$.
  
  \begin{itemize}
    \item If Alice changes $a_1$ to $a_2$ and Bob changed $a_1$ to $a_3$,
          with $a_2 \neq a_3$, we have an \emph{update-update} conflict;
    \item If Alice deletes information that was changed by Bob we have
          an \emph{delete-update} conflict;
    \item Last but not least, if Alice changes information that was deleted by Bob
          we have an \emph{update-delete} conflict.
    \item If Alice adds information to a fixed-point, this is
          a \emph{grow-left} conflict;
    \item When Bob added information to a fixed-point, which Alice didn't,
          a \emph{grow-right} conflict arises;
    \item If both Alice and Bob add different information to a fixed-point,
          a \emph{grow-left-right} conflict arises;        
  \end{itemize}
  
  Most of the readers might be familiar with the \emph{update-update},
\emph{delete-update} and \emph{update-delete} conflicts, as these are the 
most straight forward to be recognized as conflicts. We refer to these
conflicts as \emph{update} conflicts. 

  The \emph{grow} conflicts are slightly more subtle. This class of conflicts
corresponds to the \emph{alignment table} that \emph{diff3}
calculates \cite{Khanna2007} before deciding which changes go where. The idea is
that if Bob adds new information to a file, it is impossible that Alice changed
it in any way, as it was not in the file when Alice was editing it, we then flag
it as a conflict. The \emph{grow-left} and \emph{grow-right} are easy to handle,
if the context allows, we could simply transform them into actual insertions or copies.
They represent insertions made by Bob and Alice in \emph{disjoint} places of the structure.
A \emph{grow-left-right} is more complex, as it corresponds to a overlap and we
can not know for sure which should come first unless more information is provided.
  From the structure in our patch-space, we can already separate conflicts by
the types they can occur on. An \emph{update-update} conflict has to happen on a
coproduct type, for it is the only type which \F{Patch}es over it can have
multiple different options, whereas the rest are restricted to fixed-point types. In Agda,
  
  \Agda{Diffing/Patches/Conflicts}{C-def}
      
\subsection{Incorporating Conflicts}
\label{sec:conflicts}

  In order to track down these conflicts we need a more expressive patch data
structure. We exploit $D$'s parameter for that matter. This approach has the
advantage of separating conflicting from conflict-free patches on the type level,
guaranteeing that we can only \emph{apply} conflict-free patches.

  The final type of our residual\footnote{Our residual operation does not form a
residual as in the Term Rewriting System sense\cite{Bezem2003}. It might,
however, satisfy interesting properties. This is left as future work for now}.
operation is:
  
  \Agda{Diffing/Patches/Residual}{residual-type}
  
  We reiterate that the partiality comes from the fact the residual is not
defined for non-aligned patches. The whole function is too big to be shown here,
but explaining one of its cases can provide valuable intuition.

  \Agda{Diffing/Patches/Residual}{res-dwn-del-case}
  
  Here we are computing the residual:
\[ (P_x = \DmuDwn dx \cons dp) / (P_y = \DmuDel y \cons dq) \]

We want to describe how to apply the $P_x$ changes to an object
that has been modified by the $P_y$ patch. Note the order is important!
The first thing we do is to check whether or not the patch $dx$ can be applied to $y$.
If we can not apply $dx$ to $y$, then patches $P_x$ and $P_y$ are non-aligned, we
then simply return \IC{nothing}. If we can apply $dx$ to $y$, however, this will
result in an object $y'$. We then need to compare $y$ to $y'$, as if they are
different we are in a \IC{UpdDel} conflict situation. If they are equal, then $dx$
is just $\F{diff-id}\; y$, that is, no changes were performed. To extend this to 
be applied to the object were $y$ was deleted we simply suppress the $\DmuDel$ and 
continue recursively. The remaining cases follow a similar reasoning process.  

  The attentive reader might have noticed a symmetric structure on conflicts.
This is not at all by chance. In fact, we can prove that the residual of $p / q$
have the same (modulo symmetry) conflicts as $q / p$. This proof goes in two
steps. Firstly, \F{residual-symmetry} proves that if $p$ and $q$ are aligned,
that is, $p / q \equiv \IC{just}\;k$ for some $k$, then there exists a function
$op$ such that $q / p \equiv \IC{just}\;(\F{D-map}\;\F{C-sym}\; (op\;k))$. We
then prove, in \F{residual-sym-stable} that this function $op$ does not
introduce any new conflicts, it is purely structural. This could be made into a
single result by proving that the type of $op$ actually is $\forall A\; .\;
\F{D}\;A\;t\;ty \rightarrow \F{D}\;A\;t\;ty$, we chose to split it for improved
readability.
  
  \Agda{Diffing/Patches/Residual/Symmetry}{residual-symmetry-type}
  
  \Agda{Diffing/Patches/Residual/SymmetryConflict}{residual-sym-stable-type}
  
  Here \F{$\downarrow-map-\downarrow$} takes care of hiding type indexes and
\F{forget} is the canonical function with type $\F{D}\;A\;t\;ty \rightarrow
\F{List}\;(\F{$\downarrow$}\; A)$, \F{$\downarrow\_$} encapsulates the type indexes of
the different $A$'s we might come across.
    
  Now, we can compute both $p / q$ and $q / p$ at the same time. It also backs
up the intuition that using residuals or patch commutation (as in Darcs) is not
significantly different. This means that $p / q$ and $q / p$, although
different, have the same conflicts (up to conflict symmetry).

\paragraph*{Merge Strategies}

  By looking at the type of \emph{residual} we see that figure
\ref{fig:residual} does not really reflect what really happens with residuals. A
more accurate picture is given in figure \ref{fig:residualreal}, where $op$ is
the function obtained by \F{residual-symmetry} and $e$ is a special patch, lets
call it a \emph{merge strategy} for now.

  \begin{figure}[h]
  \begin{displaymath}
    \xymatrix{
         & A_0 \ar[dl]_{p} \ar[dr]^{q} &  \\
         A_1 \ar[d]_{q / p} & & A_2 \ar[d]^{p / q} \\
         P_{1/2} \ar@@{=}[rr]^{op} \ar[dr]_{e} & & P_{2/1} \ar[dl]^{e} \\
         & A_3 &      
      }
  \end{displaymath}
  \caption{Residual patch square}
  \label{fig:residualreal}
  \end{figure}
    
  Note that $P_{1/2}$ and $P_{2/1}$ are not really objects, as we can not apply
a patch with conflicts. They are patches with conflicts. In order to more clearly
discuss what is going on let us take a closer look at the types of the left path
from $A_0$ to $A_3$. We assume that $p , q : \F{Patch} A$ and $hip : q / p \equiv
\IC{just}\; k$ for some $k$, for the rest of this section. 

  In order to merge things, that is, to compute patches $p'$ and $q'$ that can be
applied to $A_1$ and $A_2$ and produce the same $A_3$ we need to figure out what
the aforementioned \emph{merge strategy} actually is. Playing around with the types of
our already defined functions we have:

\newcommand{\marr}[1]{\xrightarrow{\mathmakebox[6em]{#1}}}
\begin{eqnarray*}
  A & \marr{\text{flip}\; \F{gdiff}\; A_1} & \F{Patch}\;A \\
    & \marr{(q /)} & \F{Maybe}\;(\F{PathC}\; A) \\
    & \marr{\F{fromJust}\;hip} & \F{PatchC}\;A \\
    & \marr{e} & \F{B}\;(\F{Patch}\;A)    
\end{eqnarray*}

  By assumption and the types above, we see that a suitable type for the
\emph{merge strategy} $e$ would be $\F{PatchC}\;A \rightarrow
\F{B}\;(\F{Patch}\;A)$ for some behavior monad \F{B}. An interactive merge
strategy would have $\F{B} = |IO|$, a partial merge strategy would have $\F{B} =
\F{Maybe}$, etc. We can see that the design space is huge in order to define how
to merge patches. Ideally we would like to have a library of \emph{mergers} and
a calculus for them, such that we can prove lemmas about the behavior of some
\emph{merge strategies}, that is, a bunch of \emph{mergers} combined using
different operators.

  A simple pointwise \emph{merge strategy} can be defined for a \emph{merger} $m
: \forall \{t \; ty\} \rightarrow \Ctty \rightarrow \Dtty$, which can now be
mapped over $\DCtty$ pointwise on its conflicts. We end up with an object of
type $\F{D}\;(\F{D}\;\F{$\bot_p$})\;t\;ty$. This is not a problem, however,
since the free-monad structure on \F{D} provides us with a multiplication $\mu_D
: \F{D}\;(\F{D}\;A)\;t\;ty \rightarrow \F{D}\;A\;t\;ty$. Therefore, 
\[
merge_{pw}\;m : \DCtty \xrightarrow{\mu_D \cdot \F{D-map}\; m} \Patchtty 
\]
would be one possible \emph{merge strategy} using the \emph{merger} $m$ for
removing the conflicts of a patch. Mapping a \emph{merger} over the conflicting
patch is by far not the only possible way of walking the tree, as we shall see
in section \ref{sec:haskell}. This opens up a lot of very interesting questions
and paves the road to defining conflict resolution combinators. Allowing for a
great degree of genericity in the base framework.

\section{The Haskell Prototype}
\label{sec:haskell}

  In sections \ref{sec:cf} and \ref{sec:residual} we have layered the foundations
for creating a generic, structure aware, version control system. We proceed by illustrating
these ideas with a prototype in Haskell, with an emphasis on its extended capability
of handling non-trivial conflicts. A great advantage of using $\CF$ as a universe is
that we are able to do generic-programming via typeclasses in Haskell.

  The user has access to a typeclass |Diffable a|, which gives the basic diffing
and merging functionality for objects of type |a|:

\vskip .5em
\begin{code}
class (Sized a) => Diffable a where  
  diff   :: a -> a -> Patch a
  apply  :: Patch a -> a -> Maybe a 
  res    :: Patch a -> Patch a -> Maybe (PatchC a) 
  cost   :: Patch a -> Int
\end{code}
\vskip .5em

Where |Sized a| is a class providing the \F{sizeElU} function, presented in
section \ref{sec:cost}; |Patch| is a GADT\cite{PeytonJones2006} reflecting our \F{Patch}
type in Agda. We then proceed to provide instances by induction on the structure
of |a|. Products and coproducts are trivial and follow immediately from the Agda code.

\vskip .5em
\begin{code}
instance (Diffable a, Diffable b) 
    => Diffable (a , b)
instance (Eq a , Eq b, Diffable a , Diffable b) 
    => Diffable (Either a b)
\end{code}
\vskip .5em

Fixed points are not complicated, too. It is important that they support
the same plugging and unplugging functionality as in Agda, though.
We have to use explicit recursion since current Haskell's instance search does
not have explicit type applications yet.

\vskip .5em
\begin{code}
newtype Fix a = Fix { unFix :: a (Fix a) } 

class (Eq (a ())) => HasAlg (a :: * -> *) where   
  ar     :: Fix a -> Int
  ar     = length . ch
  ch     :: Fix a -> [Fix a]
  hd     :: Fix a -> a ()
  close  :: (a () , [Fix a]) 
         -> Maybe (Fix a , [Fix a])

instance (HasAlg (a :: * -> *) , Diffable (a ())) 
    => Diffable (Fix a)
\end{code}
\vskip .5em

All the other types can also be seen as sums-of-products. We then define
a class and some template Haskell functionality to generate instances of |SOP a|.
The \emph{overlappable} pragma makes sure that Haskell's instance search
will give preference to the other \emph{Diffable} instances, whenever the term head
matches a product, coproduct atom or fixed-point.

\vskip .5em
\begin{code}
class HasSOP (a :: *) where
  type SOP a :: *
  go :: a -> SOP a
  og :: SOP a -> a
  
instance {-# OVERLAPPABLE #-} 
    (HasSOP a , Diffable (SOP a)) 
    => Diffable a 
\end{code}
\vskip .5em

  As the tool is still a very young prototype, we chose to omit implementation
details. For those who wish to see these details, the code is available
online\footnote{\warnme{HASKELL REPOSITORY}}. There is, however, one extension we need
to be able to handle built-in types. We have two additional constructors to |Patch| 
to handle atomic types:

\vskip .5em
\begin{code}
newtype Atom a = Atom { unAtom :: a }

instance (Eq a) => Diffable (Atom a)
\end{code}
\vskip .5em

  An |Atom a| is isomorphic to |a|. The difference is that it serves as a flag
to the diff algorithm, telling it to treat the |a|'s atomically. That is, either
they are equal or different, no inspection of their structure is made. As a
result, there are only two possible ways to change an |Atom a|. We can either
copy it, or change one |x :: a| into a |y :: a|. 

\subsection{A more involved proof of concept}
  
  In order to show the full potential of our approach, we will develop a simple
example showing how one can encode and run a \emph{refactoring} conflict solver for arbitrary
datatypes. We will first introduce some simple definitions and then explore how
refactoring can happen there. We 

  Our case study will be centered on CSV files with integers on their cells. The canonical
representation of this CSV format is |T|. Moreover, we will also assume that the specific
domain in which these files are used allows for refactorings.

\vskip .5em
\begin{code}
type T = List (List (Atom Int))
\end{code}
\vskip .5em

  Our |List| type is then defined as follows:

\vskip .5em
%format DOTS = "\cdots"
\begin{code}
newtype  L a x   = L { unL :: Either () (a , x) }
type     List a  = Fix (L a)
\end{code}
\vskip .5em

%format k  = "\uparrow"
%format ki = "\hskip .3em \uparrow \hskip -.3em"
  Again, |List a| is isomorphic to |[a]|, but it uses explicit
  recursion\footnote{ The use of explicit recursion is what forces us to define
  |L| as a newtype, so that we can partially apply it.} and hence has a |HasAlg|
  and |HasSOP| instance. Both of them are trivial and hence omitted. We hence
  have that |T| is isomorphic to |[[Int]]|. We will denote |k :: [[Int]] -> T|
  as one of the witnesses of such isomorphism.

  We are now ready to go into our case study. Imagine both Alice and Bob clone
a repository containing a single CSV file |l0 = ki [[1 , 2] , [3]]|. 
Both Alice and Bob make their changes to |lA| and |lB| respectively.

\vskip .5em
\begin{code}
lA = ki [[2] , [3, 1]]
lB = ki [[12 , 2] , [3]]
\end{code}
\vskip .5em
  
  Here we see that Alice moved the cell containing the number 1 and Bob
changed 1 to 12. Lets denote these patches by |pA| and |pB| respectively.
In a simplified notation, they are represented by:

\vskip .5em
\begin{code}
  pA = [  Dwn [Del 1 , Cpy 2 , Cpy [] ] 
       ,  Dwn [Cpy 3, Ins 1, Cpy []]
       ,  Cpy []]
  pB = [  Dwn [Set 1 12 , Cpy 2 , Cpy [] ] 
       ,  Cpy [3] 
       ,  Cpy []]
\end{code}
\vskip .5em

  We will now proceed to merge these changes automatically, following the
approach on section \ref{sec:residual}, we want to propagate Alice's changes
over Bob's patch and vice-versa. There will obviously be conflicts on those
residuals. Here we illustrate a different way of traversing a patch with
conflicts besides the free-monad multiplication, as mentioned in section
\ref{sec:conflicts}. Computing |pA / pB| yields:

\vskip .5em
\begin{code}
  pA / pB = [  Dwn [DelUpd 1 12 , Cpy 2 , Cpy [] ] 
            ,  Dwn [Cpy 3, GrowL 1, Cpy []]
            ,  Cpy []]
\end{code}
\vskip .5em

  As we expected, there are two conflicts there! A $\IC{DelUpd}\;1\;12$ and a
$\IC{GrowL}\;1$ conflict on |pA / pB|. Note that the \IC{GrowL}
\emph{matches} the deleted object on \IC{DelUpd}. This is the \emph{anatomy} of
a refactoring conflict! Someone updated something that was moved by someone else. 
Moreover, from \F{residual-symmetry}, we know that that
the conflicts in |pB / pA| are exactly $\IC{UpdDel}\;12\;1$ and $\IC{GrowR}\;1$.
The grow also matches the deleted object.

  By permeating Bob's changes over Alice's refactor we would expect the the
resulting CSV to be |lR = ki [[2] , [3, 12]]|. The functorial structure of
patches provides us with exactly what we need to do so. The idea is that we
traverse the patch structure twice. First we make a list of the \IC{DelUpd} and
\IC{UpdDel} conflicts, then we do a second pass, now focusing on the \emph{grow}
conflicts and trying to match them with what was deleted. If they match, we
either copy or insert the \emph{updated} version of the object.

  Recall \ref{sec:conflicts}, where we explain that conflict solving is comprised
of a \emph{merge strategy} combining different \emph{mergers}. Although still
not formulated in Agda, our Haskell prototype library already provides different
\emph{merge strategies} and \emph{mergers}. It is worth mentioning that the actual code is slightly more complicated\footnote{
We define a \emph{subtyping} relation as a GADT, named |a :>: b|, which specifies |b| as a subtype
of |a|. The actual Haskell code uses this proofs extensively in order to typecheck
and cast conflicts instead of the rank 2 types shown here.
}, as the
generic nature of the functions require some boilerplate code to typecheck but the
main idea is precisely the same, for we will present a simplified version. 

  In the context provided by the current example, we will use a \emph{merge strategy}
|solvePWithCtx| with a \emph{merger} |sRefactor|.

%format forall = "\forall"
%format DOT    = "\cdot"
\vskip .5em
\begin{code}
sRefactor      :: Cf a -> [forall x DOT Cf x] -> Maybe (Patch a)
solvePWithCtx  :: (Cf a -> [forall x DOT Cf x] -> Maybe (Patch a))
               -> PatchC b -> PatchC b
\end{code}
\vskip .5em

  The |solvePWithCtx| \emph{merge strategy} will perform the aforementioned two
traversals. The first one records the conflicts whereas the second one applies
|sRefactor| to the conflicts. The |sRefactor| \emph{merger}, in turn, will
receive the list of all conflicts (context) and will try to match the
\emph{growths} with the \emph{deletions}. Note that we return a |PatchC| from
the \emph{merge strategy}. This happens since the \emph{merge strategy} is
\emph{partial}. It will leave the conflicts it cant solve untouched. Predicate
|resolved :: PatchC a -> Maybe (Patch a)| casts it back to a patch if no
conflict is present. We stress that the maximum we can do is provide the user
with \emph{merge strategies} and \emph{mergers}, but since different domains
will have different conflicts, it is up to the user to program the best
strategy for that particular case. We leave as future work the development
of an actual calculus of \emph{mergers}, allowing one to actually prove
their strategy will behave the way one expects.  

  We can now compute the patches |pAR| and |pBR|, to be applied to Alice's and Bob's
copy in order to obtain the result, by: 

\vskip .5em
\begin{code}
  Just pAR = resolved (solvePWithCtx sRefactor (pB / pA))
  Just pBR = resolved (solvePWithCtx sRefactor (pA / pB))
\end{code}
\vskip .5em

  Which evaluates to:  
  
\vskip .5em
\begin{code}
  pAR = [  Cpy [2] 
        ,  Dwn [Cpy 3 , Set 1 12 , Cpy []] 
        ,  Cpy []]
  pBR = [  Dwn [Del 12 , Cpy 2 , Cpy []] 
        ,  Dwn [Cpy 3 , Ins 12 , Cpy []] 
        ,  Cpy []]
\end{code}
\vskip .5em

  And finally we can apply |pAR| to Alice's copy and |pBR| to Bob's copy
and both will end up with the desired |lR = ki [[2] , [3, 12]]| as a result.

  As we can see from this not so simple example, our framework allows for a
definition of a plethora of different conflict solving strategies. This fits
very nicely with the \emph{generic} part of the diff problem we propose to
solve. In the future we would like to have a formal calculus of combinators for
conflict solving, allowing different users to fully customize how their merge
tool behaves.

\section{Summary, Remarks and Related Work}

  On this paper we presented our approach to solving the generic diffing
problem. We provided the theoretical foundations and created a Haskell prototype
applying the proposed concepts. The diffing API can be made ready for all
Haskell types, out of the box, with some simple Template Haskell, as all we need
is the derivation of two trivial instances. We have also shown how this approach
allows one to fully specialize conflict resolution for the domain in question.
The work of L\"{o}h\cite{Loh2009} and Vassena\cite{Vassena2015} are the most
similar to our. We use a drastically different definition of patches, in order
to have room for experimenting with conflict resolution.

  Below we give a short comparison with other related work.

  \begin{description}
    \item[Antidiagonal] Although easy to be confused with the diff problem,
      the antidiagonal is fundamentally different from the diff/apply
      specification. In \cite{Piponi2007}, the antidiagonal for a type $T$ is
      defined as a type $X$ such that there exists $X \rightarrow T^2$. That is,
      $X$ produces two \textbf{distinct} $T$'s, whereas a diff produces a $T$
      given another $T$. 
    
    \item[Pijul]
      The VCS Pijul is inspired by \cite{Mimram2013}, where they use the 
      free co-completion of a category to be able to treat merges as
      pushouts. In a categorical setting, the residual square (figure \ref{fig:residual})
      looks like a pushout. The free co-completion is used to make sure that for
      every objects $A_i$, $i \in \{0 , 1 , 2 \}$ the pushout exists. Still, the base
      category from which they build their results still handles files as a list
      of lines, thus providing an approach that does not take the file structure
      into account. 
      
    \item[Darcs]
      The canonical example of a \emph{formal} VCS is Darcs \cite{Darcs}. The
      system itself is built around the \emph{theory of patches} developed by
      the same team. A formalization of such theory using inverse semigroups can
      be found in \cite{Jacobson2009}. They use auxiliary objects, called
      \emph{Conflictors} to handle conflicting patches, however, it has the same
      shortcoming for it handles files as lines of text and disregards their
      structure. 
  \end{description}
  
  Finally, we address some issues and their respective solutions to the
work done so far before concluding. The implementation of these solutions and the
consequent evaluation of how they change our theory of patches
is left as future work.

\subsection{Cost, Inverses and Lattices}
\label{sec:costremarks}

  Back in section \ref{sec:cost}, where we calculated our cost function from a
specification, we did not provide a formal proof that our definitions
did in fact satisfy the relation we stated:

\[ \F{dist}\;x'\;y' < c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y') < c_\oplus\;(i_j\;x')\;(i_k\;y') \]

  This is, in fact, deceptively complicated. Since \F{$\_\lubmu\_$} is not
commutative nor associative, in general, we do not have much room to reason
about the result of a \F{gdiffL}. A more careful definition of \F{$\_\lubmu\_$}
that can provide more properties is paramount for a more careful study of the
\F{cost} function. Defining \F{$\_\lubmu\_$} in such a way that it gives us a
lattice over patches and still respects patch inverses is very tricky, as for
making it preserve inverses we need to have $\F{D-inv}(d_1 \F{$\lubmu$} d_2)
\equiv \F{D-inv}\;d_1 \F{$\lubmu$} \F{D-inv}\;d_2$. A simpler option would be to
aim for a quasi-metric $d$ instead of a metric (dropping symmetry; equation
(2)), this way inverses need not to distribute over \F{$\_\lubmu\_$} and we can
still define a metric $q$, but now with codomain $\mathbb{Q}$, as $q\;x\;y =
\frac{1}{2}(d\;x\;y - d\;y\;x)$.

\subsection{A remark on Type Safety}
\label{sec:typesafety}

  The main objectives of this project is to release a solid diffing and merging
tool, that can provide formal guarantees, written in Haskell. The universe of
user-defined Haskell types is smaller than context free types; in fact, we have
fixed-points of sums-of-products. Therefore, we should be able to apply the
knowledge acquired in Agda directly in Haskell. In fact, we did so! With a few
adaptations here and there, to make the type-checker happy, the Haskell code is
almost a direct translation. There is one minor detail we would like to point
out in our approach so far. Our \F{D$\mu$} type admits ill-formed patches.
Consider the following simple example:

  \Agda{Diffing/Patches/IllDiff}{ill-patch-example}
  
  On \F{ill-patch} we try to insert a \IC{suc} constructor, which require one recursive
argument, but then we simply end the patch. Agda realizes that this patch will
lead nowhere in an instant.

  Making \F{D$\mu$} type-safe by construction should be simple. The type of the functor
is always fixed, the telescope too. Hence they can become parameters. We just need 
to add two \F{$\mathbb{N}$} as indexes.

  \Agda{Diffing/Postulated}{Dmu-type-safe-type}

  Then, $\F{D$\mu$}\;A\;t\;ty\;i\;j$ will model a patch
over elements of type $T = \F{ElU} (\IC{$\mu$}\;ty)\;t$ and moreover, it expects a
vector of length $i$ of $T$'s and produces a vector of length $j$ of $T$'s.
This is very similar to how type-safety is guaranteed in \cite{Loh2009}, 
but since we have the types fixed, we just need the arity of their elements. 

  If we try to encode this in Agda, using the universe of context-free types, we
run into a very subtle problem. In short, we can not prove that if two elements of
a recursive type come from the same constructor then they have the same arity. 
Mainly because this does not hold! This hinders \F{D$\mu$-dwn} useless. Let us
take a look at how one defines rose trees in \CF:

  \Agda{Diffing/Universe/Syntax}{rt-def}
  
Rose trees of $a$ have a single constructor that takes an $a$ and a list of
rose trees of $a$ to produce a single rose tree. Lets call its constructor $RT$. 
However, the arity of an element of a rose tree will vary. More precisely, 
it will be equal to the length of the
list of recursive rose trees. We therefore can have two \emph{heads} coming from the
same constructor, as there is only one, with different arities, as we can see in:

  \AgdaI{Diffing/Universe/MuUtils}{rt-els-def}{-2.2em}
  
  \AgdaI{Diffing/Universe/MuUtils}{r-ar-lemma}{-2.2em}

If we look at \F{rt}'s Haskell counterpart, |data RT a = RT a [RT a]|, we see that 
its arity should be zero, as the type |RT a| does not appear immediately on
the constructor, but only as an argument to the List type.

Although easy to describe, this problem is deeper than what meets the eye. 
On a separate example, consider a leaf tree, \F{ltree}, as defined below:

  \Agda{Diffing/Universe/Syntax}{ltree-def}
  
  The Haskell equivalent, with explicit recursion, would be:
  \vskip .2em
  
\begin{code}
data LTreeF a b x  = Leaf a | Fork b x x
type LTree a b     = Fix (LTreeF a b)
\end{code}
\vskip .5em
  
  Now consider the following reduction.

  \Agda{Diffing/Universe/Syntax}{U-monster}

%format MCM = "\mathcal{M}"
 In \CF, due to the dependency introduced by the telescopes, this type of
reduction is establishing a relation between the two type variables of \F{ltree}.
Here we have the type of \F{ltree}s where the first type variable is actually
a list of the second. In Haskell, this type would be defined as |type MCM a = LTree a [a]|. 

To be able to encode this more delicate definition of arity we need to first
divide our universe into sums-of-products, so that we have the notion of 
a constructor. Then change the definition of telescope to use closed types only
(that is, types with \IC{zero} type variables), not allowing this functional dependency
between type variables. There are multiple ways to achieve this, we leave
the exploration of these techniques as future work.
  
\section{Conclusion}

  We believe that by incorporating the changes proposed in sections
\ref{sec:costremarks} and \ref{sec:typesafety}, we will be able to prove further
results about our constructions. In particular we conjecture that our
\emph{residual} operation, section \ref{sec:residual}, constitutes, in fact, a
residual system as in \cite{Tieleman2006,Bezem2003}. Moreover, we expect to be
able to formulate more accurate properties about which conditions a \emph{merge
strategy}, section \ref{sec:residual}, must satisfy in order to converge.
Moreover, we would like to have a formal categorical framework to speak about
diffs. 
  
  From our proposals, we see that it is already possible to have much better
merge tools to help automate the management of structured data. The applications
are multiple. We can use our algorithms to create specialized merge tools for
virtually every structured file format, as we just need a Haskell representation
of this data to be able to diff it. This approach is easy to integrate on the
already existing software version control systems but also allows us to develop
one from scratch, for files and directories can also be represented in Haskell.
Besides actual version control, we can also use the notion of \F{cost} we
developed for a range of topics, given that we can always compute a non-trivial
distance between values of an arbitrary datatype. 
  
  %% WARNING: Do NOT change the next comment, it's a tag for sed to
  %% glue the bibliography.
  
  %%%!BIBHOOK!%%%
  

\end{document}
