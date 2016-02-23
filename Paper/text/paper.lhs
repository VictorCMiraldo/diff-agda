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
\preprintfooter{some iformation here...}
\titlebanner{DRAFT}

\title{Structure aware version control}
%\subtitle{42}

\authorinfo{Victor Cacciari Miraldo \and Wouter Swierstra}
  {University of Utrecht}
  {\{v.cacciarimiraldo,w.s.swierstra\} at uu.nl}

\maketitle

\begin{abstract}
stuff
\end{abstract}

\category{D.1.1}{look}{for}[this]

\terms
Haskell

\keywords
Haskell

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
line-based diffs generally work well when monitoring source code, not
all data is best represented as lines of text.

Consider the following example CSV file, recording the marks and names
three students:
\begin{verbatim}
Student name, Student number, Mark
Alice   , 440, 7.0
Bob     , 593, 6.5
Carroll , 168, 8.5
\end{verbatim}
A new entry to this CSV file will not modify any existing entries and
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
  \item We define a \emph{type-indexed} data type for representing edits to
        structured data. The structure of the data closely resembles the way
        one defines data-types in functional languages such as Haskell.

  \item We define generic algorithms for computing and applying a diff
        generically and prove they are correct with respect to each other.


  \item A notion of residual is used to propagate changes of different diffs,
        hence providing a bare mechanism for merging and conflict resolution.

  \item We illustrate how these ideas in Agda have been implemented in a
        prototype Haskell tool, capable of automatically merging changes to
        structured data. This tool provides the user with the ability to define
        custom conflict resolution strategies when merging changes to structured
        data. \warnme{Cloning and swapping}
\end{itemize} 


% Move this to related work?
%  structural diff that is not only generic but also able to
% track changes in a way that the user has the freedom to decide which
% is the fundamental editing unit. Our work was inspired by
% \cite{Loh2009} and \cite{Vassena2015}. We did extensive changes in
% order to handle structural merging of patches. We also propose
% extensions to this algorithm capable of detecting purely structural
% operations such as refactorings and cloning.
    

\subsection*{Background}

\begin{TODO}
  \item Should we have this section? It cold be nice
        to at least mention the edit distance problem and that
        in the untyped scenario, the best running time is of $O(n^3)$.
        Types should allow us to bring this time lower.
\end{TODO}
  
\section{Structural Diffing}  
  
  \begin{TODO}
    \item Diffing and tree-edit distance are very closely related problems.
    \item This should go on background, though.
  \end{TODO}
  
  \begin{RESEARCH}
    \item The LCS problem is closely related to diffing.
          We want to preserve the LCS of two structures!
          How does our diffing relate?
          Does this imply maximum sharing?
          \RESEARCHAnswer{No! We don't strive for
            maximum sharing. We strive for
            flexibility and customization.
            See refactoring}
  \end{RESEARCH}
  
  To make version control to be structure aware we need to define what
structures we can handle. In our case, the structure is the universe of context
free types, patching will be defined for its inhabitants.
  
\newcommand{\CF}{\text{CF}}
\subsection{Context Free Datatypes}
\label{sec:cf}

  The universe of \emph{context-free types}, in the sense of
\cite{Altenkirch2006}, is constructed following the grammar $\CF$ of
context free types with a deBruijn representation for variables.
  
  \[
    \CF ::= 1 \mid 0 \mid \CF \times \CF \mid \CF + \CF \mid \mu \; \CF \mid \mathbb{N}
              \mid (\CF \; \CF) \mid \CF \CF
  \]
  
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
constructor to handle finite types: \IC{void}, \IC{inl}, \IC{inr} and \IC{$\_,\_$}.
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
turns out to be very expressive, providing a plethora of interesting operations.
The first very usefull concept is the decidability of generic 
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
  
  We can even go a step further and say that every element is defined by a constructor
and a vector of children, with the correct arity. This lets us treat generic elements as
elements of a (typed) rose-tree, whenever thas is convenient.

  \Agda{Diffing/Universe/Ops}{unplug-type}
  
  \Agda{Diffing/Universe/Ops}{plug-type}
  
  \Agda{Diffing/Universe/Ops}{plug-correct-type}
  
  These operations are central to solving the diffing problem, for we need
a way of traversing generic trees in order to decide how to change one into the other.
We do things a bit differently, though. We linearize the trees and proceed to traverse
the resulting list.

  For the readers familiar with Haskell's \emph{Uniplate}\cite{UNIPLATE} library,
our \F{plug} and \F{unplug} operations allow for a similar view over datatypes.
For instance, we can define the \F{transform} function in Agda as: 

  \Agda{Diffing/Universe/Lab}{transform-type}
  
  Note that we first need to pattern-match on the telescope, as types with
zero variables can not be \emph{unpluged}. 
  
  \begin{TODO}
    \item Vassena's and Loh's universe is the typed rose-tree! Correlate!!
  \end{TODO}
  
  This repertoire of operations, and the hability to inspect an element structurally,
according to its type, gives us the toolset we need in order to start describing
differences between elements. That is, we can now start discussing what does it mean
to \emph{diff} two elements or \emph{patch} an element according to some description
of changes.  
  
\subsection{Patches over a Context Free Type}

  A patch over $T$ is an object that describe possible changes that can
be made to objects of type $T$. The high-level idea is that diffing two
objects $t_1 , t_2 : T$ will produce a patch over $T$, whereas applying
a patch over $T$ to an object will produce a $Maybe\;T$. It is interesting
to note that application can not be made total. Let's consider $T = X + Y$,
and now consider a patch $(Left\; x) \xrightarrow{p} (Left\; x')$. 
What should be the result of applying $p$ to a $(Right\; y)$? It is undefined!

  The type of \emph{diff}'s is defined by \F{D}. It is indexed by a type
and a telescope, which is the same as saying that we only define \emph{diff}'s for
closed types\footnote{Types that do not have any free type-variables}. However,
it also has a parameter $A$, this will be addressed later.

  \Agda{Diffing/Patches/Diff/D}{D-type}
  
  As we mentioned earlier, we are interested in analizing the set of possible
changes that can be made to objects of a type $T$. These changes depend on
the structure of $T$, for the definition follows by induction on it.

  If $T$ is the Unit type, we can not modify it.

  \Agda{Diffing/Patches/Diff/D}{D-void-def}
  
  If $T$ is a product, we need to provide \emph{diffs} for both
its components.

  \Agda{Diffing/Patches/Diff/D}{D-pair-def}
  
  If $T$ is a coproduct, things become slighlty more interesting. There
are four possible ways of modifying a coproduct, which are defined by:

  \Agda{Diffing/Patches/Diff/D}{D-sum-def}
  
  Let us take a closer look at the diffs of a coproduct. There are two options
we can take when modifying a coproduct $a\;\IC{$\oplus$}\;b$. Given some 
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
  
  The aforementioned parameter $A$ goes is used in a single consrtuctor,
allowing us to have a free-monad structure over \F{D}'s. This shows to be
very usefull for adding extra information, as we shall discuss, on section 
\ref{sec:conflicts}, for adding conflicts.

  \Agda{Diffing/Patches/Diff/D}{D-A-def} 
 
  Finally, we define $\Patchtty$ as $\F{D}\;(\lambda \;\_\;\_ \rightarrow \bot)\; t\; ty$.
Meaning that a \F{Patch} is a \F{D} with \emph{no} extra information.

\subsection{Producing Patches}  
  
  Given a generic definition of possible changes, the primary goal is to produce
an instance of this possible changes, for two specific elements of a type $T$.
We shall call this process \emph{diffing}. It is important to note that
our \F{gdiff} function expects two elements of the same type! This constrasts
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
  
  But the interesting bits are the \emph{edit operations} we allow,
where $\F{Val}\;a\;t = \F{ElU}\;a\;(\IC{tcons}\;\IC{u1}\;t)$:
  
  \Agda{Diffing/Patches/Diff/D}{Dmu-def}
  
  Again, we have a constructor for adding \emph{extra} information, which is
ignored in the case of \F{Patches}.

  \Agda{Diffing/Patches/Diff/D}{Dmu-A-def}
  
  The edit operations we allow are very simple. We can add or remove parts
of a fixed-point or we can modify non-recursive parts of it.
and instead of copying, we introduce a new constructor, \IC{D$\mu$-dwn}, which
is responsible for traversing down the type-structure. Copying is modelled by
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
  
  Although the \F{plug} and \F{unplug} uses vectors, to remain total functions,
we drop that restriction and switch to lists instead, this way we can easily
construct a fixed-point with the beginning of the list of children, and return
the unused children, this will be very conveient when defining how patches are applied. 
Nevertheless, a soundness lemma guarantees the correct behaviour.
  
  \Agda{Diffing/Universe/MuUtils}{mu-close-resp-arity-lemma}
  
  We denote the first component of an \emph{opened} fixed point by its
\emph{value}, or \emph{head}; whereas the second component by its children. The
diffing of fixed points, which was heavily inspired by \cite{Loh2009}, is then
defined by:
  
  \Agda{Diffing/Patches/Diff}{gdiffL-def}  
  
\newcommand{\lubmu}{\sqcup_{\mu} \;}
\newcommand{\Flubmu}{\; \F{$\lubmu$} \;}
  The first three branches are simple. To transform |[]| into |[]|, we do not
need to perform any action; to transform |[]| into |y : ys|, we need to insert
the respective values; and to transform |x : xs| into |[]| we need to delete the
respective values. The interesting case happens when we want to transform |x:xs|
into |y:ys|. Here we have three possible diffs that perform the required transformation. 
We want to choose the diff with the least \emph{cost}, for
we introduce an operator to do exactly that:

  \Agda{Diffing/Patches/Diff/Cost}{lubmu-def}

As we shall see in section \ref{sec:cost},
this notion of cost is very delicate. The idea, however, is simple. If the heads
are equal we have $d3 = \IC{D$\mu$-dwn}\; (\F{gdiff}\; hdX\; hdX) \cdots$, which
is how copy is implemented. We want to copy as much as possible, so we will ensure 
that for all $a$, $\F{gdiff}\;a\;a$, that is, the identity patch for $a$, has cost 0 whereas \IC{D$\mu$-ins} and \IC{D$\mu$-del} will have strictly positive cost.

Since we mentioned \emph{the identity patch} for an object, we might already introduce 
the two \emph{special} patches that we need before talking about \F{cost}.

\paragraph*{The Identity Patch}
\label{sec:id}

  Given the definition of \F{gdiff}, it is not hard to see that whenever
$x \equiv y$, we produce a patch without any \IC{D-setl}, \IC{D-setr},
\IC{D$\mu$-ins} or \IC{D$\mu$-del}, let us call these the \emph{change-introduction} constructors. 
Well, one can spare the comparisons made by \F{gdiff} and trivially define the
identity patch for an object $x$, $\F{gdiff-id}\; x$, by induction on $x$. A
good sanity check, however, is to prove that this intuition is in fact correct:
  
  \Agda{Diffing/Patches/Diff/Id}{gdiff-id-correct-type}
  
\paragraph*{The Inverse Patch} 

  If a patch $\F{gdiff}\;x\;y$ is not the identity, then it has \emph{change-introduction} constructors.
if we swap every \IC{D-setl} for \IC{D-setr}, and \IC{D$\mu$-ins} for \IC{D$\mu$-del} and
vice-versa, we get a patch that transforms $y$ into $x$. We shall call this operation the inverse
of a patch.

  \Agda{Diffing/Patches/Diff/Inverse}{D-inv-type}
  
  As one would expect, $\F{gdiff}\;y\;x$ or $\F{D-inv}\;(\F{gdiff}\;x\;y)$
should be the same patch. In fact, we have that $\F{gdiff}\;y\;x \approx \F{D-inv}\;(\F{gdiff}\;x\;y)$.
That is to say $\F{gdiff}\;y\;x$ behaves the same as $\F{D-inv}\;(\F{gdiff}\;x\;y)$,
but may not be identitcal. In the presence of equal cost alternatives they may make
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
with no \emph{change-introcution} constrcutor.

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
we can see that this is trivially satisfied. Let us denote the number of 
\emph{change-introduction} constructors in a patch $p$ by $\# p$. In the best case scenario,
$\# (\F{gdiff}\;x\;y) + \# (\F{gdiff}\;y\;z) = \# (\F{gdiff}\;x\;z)$, this is the situation
in which the changes of $x$ to $y$ and from $y$ to $z$ are non-overlapping. If they
are overlapping, then some changes made from $x$ to $y$ must be changed again from $y$ to $z$,
yielding $\# (\F{gdiff}\;x\;y) + \# (\F{gdiff}\;y\;z) > \# (\F{gdiff}\;x\;z)$. 

  \vskip .3em

  From equations (1) and (2) and from our definition of the equality patch and
the inverse of a patch we already have that:

  \Agda{Diffing/Patches/Diff/Id}{gdiff-id-cost-type}
  
  \Agda{Diffing/Patches/Diff/Inverse}{D-inv-cost-type}
  
  In order to finalize our definition, we just need to find an actual value for
$c_\oplus$ and $c_\mu$. Note that we have a lot of freedom to choose these values.
And in fact, they are what is going to drive the diff algorithm to prefer some
changes over others. Let us then take a look at where the difference between
these values comes into play, and calculate from there. 
Assume we have stopped execution of \F{gdiffL} at
the $d_1 \Flubmu d_2 \Flubmu d_3$ expression. Here we have three patches to
choose from:

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
inserting and deleting should be the same, the analisys for $d_2$ is analogous.
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

  Hence, \F{cost }$d_1$ is $c_\mu\;hdX + c_\mu\;hdY + w$, for $w = \F{cost}\;(\F{tail}\;d_3)$.
Obviously, $hdX$ and $hdY$ are values of the same type. Namelly $hdX , hdY : \F{ElU}\;ty\;(\IC{tcons}\;\IC{u1}\;t)$. Since we want to apply this to Haskell datatypes by the end of the day, it is acceptable
to assume that $ty$ is a coproduct of constructors. 
Hence $hdX$ and $hdY$ are values of the same finitary coproduct, representing
the constructors of the fixed-point datatype. If $hdX$ and $hdY$ comes from different 
constructors of our fixed-point datatype in question,
then\footnote{
%%%% FOOTNOTE
We use $i_j$ to denote the $j$-th injection into a finitary coproduct. 
%%%% FOOTNOTE
} $hdX = i_j\; x'$ and $hdY = i_k\; y'$ where $j \neq k$. The patch from $hdX$ to $hdY$ will
therefore involve a $\IC{D-setl}\;x'\;y'$ or a $\IC{D-setr}\;y'\;x'$, hence
the cost of $d_3$ becomes $c_\oplus\;x'\;y' + w$. Remember that in this situation
it is wise to delete and insert instead of recursively changing. Since things are comming
from a different constructors the structure of the outermost type
is definetely changing, we want to reflect that! This means we need to select $d_1$
instead of $d_3$, hence:

\[
\begin{array}{crcl}
  & c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y') + w & < & c_\oplus\;(i_j\;x')\;(i_k\;y') + w \\
  \Leftrightarrow & c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y') & < & c_\oplus\;(i_j\;x')\;(i_k\;y')
\end{array}
\]

  If $hdX$ and $hdY$ come from the same constructor, on the other hand, the story
is slightly different. We now have $hdX = i_j\;x'$ and $hdY = i_j\;y'$, the cost
of $d_1$ still is $c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y') + w$ but the cost of $d_3$ 
is $\F{dist}\;x'\;y' + w$, since $\F{gdiff}\;hdX\;hdY$ will be $\F{gdiff}\;x'\;y'$ preceded by a sequence
of \IC{D-inr} and \IC{D-inr} since $hdX$ and $hdY$ they come from the same coproduct injection,
but these have cost 0. This is the situation that selecting $d_3$ might be a wise choice,
therefore we need:

\[
\begin{array}{crcl}
  & \F{dist}\;x'\;y' + w & < & c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y') + w \\
  \Leftrightarrow & \F{dist}\;x'\;y' & < & c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y')
\end{array}
\]

In order to enforce this behaviour on our diffing algorithm, we need to assign
values to $c_\mu$ and $c_\oplus$ that respects:

\[ \F{dist}\;x'\;y' < c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y') < c_\oplus\;(i_j\;x')\;(i_k\;y') \]

Note that there are an infinite amount of definitions that would fit here. This is
indeed a central topic of future work, as the \F{cost} function is what drives
the diffing algorithm. So far we have calculated a relation between $c_\mu$ and $c_\oplus$ that
will make the diff algorithm match in a top-down manner. That is, the outermost
type is seen as the heaviest change. Different domains may require a different
relation. For a first generic implementation, however, this relation does make sense.
Now is the time for assigning values to $c_\mu$ and $c_\oplus$ and the diffing
algorithm is completed. We simply define the cost function in such a way that it
has to satisfy the constraints we imposed.

  \Agda{Diffing/Patches/Diff/Cost}{cost-def}
  
  Where $\F{costL} = sum \cdot map\; \F{cost$\mu$}$ and the size of an element is defined by:
  
  \Agda{Diffing/Universe/Measures}{sizeEl}

\subsection{A Small Example}

\begin{TODO}
  \item add context
\end{TODO}

\begin{enumerate}[I)]
    \item Copy the first line;
    \item Enter the second line;
      \begin{enumerate}[i)]
        \item Copy the first field;
        \item Enter the second field;
          \begin{itemize}
            \item Update atom |"1"| for atom |"2"|.
          \end{itemize}
        \item Copy the third field;
      \end{enumerate}
    \item Copy the third line.
    \item Finish.
\end{enumerate}
  
In figure \ref{fig:alicespatch} we show the patch that corresponds to that.

\begin{figure}[h]
\begin{center}
\begin{tabular}{m{.17\textwidth} m{.6\textwidth}}
\csvABlbl{\begin{tabular}{lll}
items & qty & unit \\
flour & 1   & cp   \\
eggs  & 2   & units
\end{tabular}}{\begin{tabular}{lll}
items & qty & unit \\
flour & 2    & cp  \\
eggs  & 2    & units 
\end{tabular}}{Alice}
 &
  $ \begin{array}{l l}
  Cpy & | ["items" , "qty" , "unit" ] | \\
  Dwn & \left\{ \begin{array}{l l} 
            Cpy & |"flour"| \\ 
            Dwn & Upd \; | "1" "2" | \\
            Cpy & |"cp"| \\
            End &
         \end{array} \right. \\
  Cpy & | ["eggs" , "2" , "units"] | \\
  End &
 \end{array} $    
\end{tabular}
\end{center}
\caption{Alice's Patch}
\label{fig:alicespatch}
\end{figure}

  Consider now Bob's structural changes to the CSV file\footnote{Exercise to the
reader! Clue: the last two operations are $Ins\;|["sugar" , "1" , "tsp"]|\;End$}. If you overlap
both, you should notice that there is $Upd$ operation on top of another. This
was in fact expected given that Alice and Bob performed changes in disjoint
parts of the CSV file.

\subsection{Applying Patches}
\label{sec:apply}

  At this stage we are able to: work generically on a suitable universe; describe
how elements of this universe can change and compute those changes. In order to
make our framework useful, though, we need to be able to apply the patches we
compute. The application of patches is easy, for we will only
show the implementation for coproducts and fixedpoints here. The rest is very
straightforward.

  \begin{agdacode}
  \AgdaRaw{Diffing/Patches/Diff}{gapply-type}
  \AgdaRaw{Diffing/Patches/Diff}{gapply-sum-def}
  \AgdaRaw{Diffing/Patches/Diff}{gapply-mu-def}
  \AgdaDots
  \end{agdacode}
  
  \Agda{Diffing/Patches/Diff}{gapplyL-def}
  
  Where \F{<M>} is the applicative-style application for the \emph{Maybe} monad;
\RF{>>=} is the usual bind for the \emph{Maybe} monad and \F{safeHead} is the 
partial head function with type |[a] -> Maybe a|. In \F{gapplyL}, we have
a \F{gIns} function, which will get a head and a list of children of a
fixed point, will try to \F{$\mu$-close} it and add the result to the
head of the remaining list. On the other hand, \F{gDel} will \F{$\mu$-open}
the first element of the received list, compare it with the current head
and return the tail of the input list appended to its children. 

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
  
  Also relevant is the fact that the inverse of a patch behaves as it should:
  
  \Agda{Diffing/Patches/Diff/Inverse}{D-inv-sound-type}
  
  We have given algorithms for computing and applying differences over
elements of a generic datatype. Moreover, we proved our algorithms are correct
with respect to each other. This functionality is necessary for constructing
a version control system, but it is by no means sufficient!
   
\section{Patch Propagation}
\label{sec:residual}

  In a nutshell, any version control system must accomplish two tasks: (A) we
need to be able to produce and apply patches and (B) we need to be able to merge
different, concurrent, changes make to the same object. We have taken care
of task (A) in the previous sections, and even though current VCS tools
already excel at it, there is a big lack of tools exceling at (B). 
All the structural information we are using in task (A) is, in fact,
providing a lot more to help us at task (B), as we shall discuss in this section.

  
  The task of merging changes arise when we have multiple users changing the same file
at the same time. Imagine Bob and Alice perform concurrent edits in an object $A_0$, which are captured by
patches $p$ and $q$. The center of the repository needs to keep only one copy
of that object, but upon receiving the changeset of both Bob and Alice we have:

  \[ \xymatrix{ A_1 & A_0 \ar[l]_{p} \ar[r]^{q} & A_2} \]

  Our idea is to imcorporate the changes expressed by $p$ into a new patch,
namelly one that is aimed at being applied somewhere already changed by $q$,
and vice-versa, in such a way that they converge. We call this the residual patch. 
The diagram in figure \ref{fig:residual} illustrates the result of merging $p$ and $q$
through propagation.
  
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
is, $p_{alice} / p_{bob}$.
  
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
it in any way, as it was not in the file when Alice was eiditing it, we then flag
it as a conflict. The \emph{grow-left} and \emph{grow-right} are easy to handle,
if the context allows, we could simply transform them into atual insertions or copies.
They represent insertions made by Bob and Alice in \emph{disjoint} places of the structure.
A \emph{grow-left-right} is more complex, as it corresponds to a overlap and we
can not know for sure which should come first unless more information is provided.
  From the structure in our patch-space, we can already separate conflicts by
the types they can occur on. An \emph{update-update} conflict has to happen on a
coproduct type, whereas the rest are restricted to fixed-point types. In Agda,
  
  \Agda{Diffing/Patches/Conflicts}{C-def}
  
  \begin{TODO}
    \item Pijul has this notion of handling a merge as a pushout,
          but it uses the free co-completion of a rather simple category.
          This doesn't give enough information for structured
          conflict solving.
    \item BACK THIS UP!
  \end{TODO}
    
\subsection{Incorporating Conflicts}
\label{sec:conflicts}

  In order to track down these conflicts we need a more expressive patch data
structure. We exploit $D$'s parameter for that matter. This approach has the
advantage of separating conflicting from conflict-free patches on the type level,
guaranteing that we can only \emph{apply} conflict-free patches.

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
This is not at all by chance. In fact, we can prove that the residual of
$p / q$ have the same (modulo symmetry) conflicts as $q / p$. This proof
goes in two steps. Firstly, \F{residual-symmetry} proves that the symmetric
of the conflicts of $p / q$ appear in $q / p$, but this happens modulo
a function. We then prove that this function does not introduce any new conflicts,
it is purely structural. 
  
  \Agda{Diffing/Patches/Residual/Symmetry}{residual-symmetry-type}
  
  \Agda{Diffing/Patches/Residual/SymmetryConflict}{residual-sym-stable-type}
  
  Here \F{$\downarrow-map-\downarrow$} takes care of hiding type indexes and
\F{forget} is the cannonical function with type $\F{D}\;A\;t\;ty \rightarrow
\F{List}\;(\F{$\downarrow$}\; A)$, \F{$\downarrow\_$} encapsulates the type indexes of
the different $A$'s we might come accross.
    
  Now, we can compute both $p / q$ and $q / p$ at the same time. It also
backs up the intuition that using residuals or patch commutation (as in darcs) is
not significantly different.
  
  This means that $p / q$ and $q / p$, although different, have the same conflicts
(up to symmetry). Hence, we can (informally) define a \emph{merge strategy} as a function 
$m : \forall \{t \; ty\} \rightarrow \Ctty \rightarrow \Dtty$, which can
now be mapped over $\DCtty$ pointwise on its conflicts. We end up
with an object of type $\F{D}\;(\F{D}\;\F{$\bot_p$})\;t\;ty$. This is not
a problem, however, since the free-monad structure on \F{D} provides
us with a multiplication $\mu_D : \F{D}\;(\F{D}\;A)\;t\;ty \rightarrow \F{D}\;A\;t\;ty$.
Therefore, $merge_1\;m : \DCtty \xrightarrow{\mu_D \cdot D\; m} \Patchtty$ is one possible \emph{merge tool}
for removing the conflicts of a patch. Mapping $m$ over the conflicting patch is
by far not the only possible way of walking the tree, as we shall see in section \ref{sec:haskell}.
This opens up a lot of very interesting questions and paves the road to defining
conflict resolution combinators. Allowing for a great degree of genericity in
the base framework.

\section{A Haskell Prototype}
\label{sec:haskell}

  In sections \ref{sec:cf} and \ref{sec:residual} we have layed the foundations
for creating a functional version control system. We proceed by illustrating
these with a prototype in Haskell, with an emphasis on its extended capability
of handling conflicts.

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
section \ref{sec:cost}; |Patch| is a GADT\cite{GATS} reflecting our \F{Patch}
type in Agda. We then proceed to provide instances by induction on the structure
of |a|. Products and coproducs are trivial and follow immediatly from the Agda code.

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
will give preference to the other instances.

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

As the tool is still a very young prototype, we chose to ommit implementation details
such as memoization or explicit 

\subsection{A more involved example}

  \begin{TODO}
    \item Show how refactoring works
  \end{TODO}

\section{Sketching a Control Version System}

  \begin{itemize}
    \item Different views over the same datatype will give different diffs.
    \item |newtype| annotations can provide a gread bunch of control over the algorithm.
    \item Directories are just rosetrees...
  \end{itemize}

\section{Summary, Remarks and Related Work}

  \begin{RESEARCH}
  \item Check out the antidiagonal with more attention: 
          \url{ http://blog.sigfpe.com/2007/09/type-of-distinct-pairs.html }
        \RESEARCHAnswer{Diffing and Antidiagonals are
          fundamentally different. The antidiagonal for
          a type $T$ is a type $X$ such that there
          exists $X \rightarrow T^2$. That is, $X$ produces
          two \textbf{distinct} $T$'s, whereas
          a diff produces a $T$ given another $T$!}
  \end{RESEARCH}

  \begin{TODO}
    \item related work goes here!
    \item Add some boilerplate to the shameful part of the paper...
  \end{TODO}

\subsection{Cost, Inverses and Lattices}

  Back in section \ref{sec:cost}, where we calculated our cost function from a
specification, we did not provide a formal proof that our definitions
did in fact satisfy the relation we stated:

\[ \F{dist}\;x'\;y' < c_\mu\;(i_j\;x') + c_\mu\;(i_k\;y') < c_\oplus\;(i_j\;x')\;(i_k\;y') \]

  This is, in fact, deceptively complicated. Since \F{$\_\lubmu\_$} is 
not commutative nor associative, in general, we do not have much room to reason
about the result of a \F{gdiffL}. A more careful definition of \F{$\_\lubmu\_$} that can provide
more properties is paramount for a more careful study of the \F{cost} function.
Defining \F{$\_\lubmu\_$} in such a way that it gives us a lattice over patches
and still respects patch inverses is very tricky, as for making it preserve inverses
we need to have $\F{D-inv}(d_1 \F{$\lubmu$} d_2) \equiv \F{D-inv}\;d_1 \F{$\lubmu$} \F{D-inv}\;d_2$. 
A simpler option would be to aim for a 
quasi-metric $d$ instead of a metric (dropping symmetry; equation (2)), this way inverses need not
to distribute over \F{$\_\lubmu\_$} and we can still define a metric $q$, but now with codomain $\mathbb{Q}$,
as $q\;x\;y = \frac{1}{2}(d\;x\;y - d\;y\;x)$.

\subsection{A remark on Type Safety}
\label{sec:typesafety}

  The main objectives of this project is to release a 
solid diffing and merging tool, that can provide formal guarantees, written in Haskell.
The universe of user-defined Haskell types is smaller than context free types;
in fact, we have fixed-points of sums-of-products. Therefore, we should be able
to apply the knowledge acquired in Agda directly in Haskell. In fact, we did so!
With a few adaptations here and there, to make the type-checker happy, the
Haskell code is almost a direct translation. There is one minor detail we would
like to point out in our approach so far. Our \F{D$\mu$} type
admits ill-formed patches. Consider the following simple example:

  \Agda{Diffing/Patches/IllDiff}{ill-patch-example}
  
  On \F{ill-patch} we try to insert a \IC{suc} constructor, which require one recursive
argument, but then we simply end the patch. Agda realizes that this patch will
lead nowhere in an instant.

  Making \F{D$\mu$} type-safe by construction should be simple. The type of the functor
is always fixed, the telescope too. These can become parameters. We just need 
to add two \F{$\mathbb{N}$}.

  \Agda{Diffing/Postulated}{Dmu-type-safe-type}

  Then, $\F{D$\mu$}\;A\;t\;ty\;i\;j$ will model a patch
over elements of type $T = \F{ElU} (\IC{$\mu$}\;ty)\;t$ and moreover, it expects a
vector of length $i$ of $T$'s and produces a vector of length $j$ of $T$'s.
This is very similar to how type-safety is guaranteed in \cite{Loh2009}, 
but since we have the types fixed, we just need the arity of their elements. 

  If we try to encode this in Agda, using the universe of context-free types, we
run into a very subtle problem. In short, we can not prove that if two elements
come from the same constructor, they have the same arity. This hinders
\F{D$\mu$-dwn} useless. To fix this, we need to add kinds to our universe.
Context-free type aplication does not behave the same way as in Haskell.
Consider \F{list} as defined in section \ref{sec:cf} and \F{ltree} as defined
below.

  \Agda{Diffing/Universe/Syntax}{ltree-def}
  
  The Haskell equivalent, with explicit recursion, would be:
  
\begin{code}
data LTreeF a b x  = Leaf a | Fork b x x
type LTree a b     = Fix (LTreeF a b)
\end{code}
\vskip .5em
  
  The kind of |LTree| is $\star \Rightarrow \star \Rightarrow \star$. Hence,
it can only receive arguments of kind $\star$. In \CF, however, we
can apply \F{ltree} to \F{list}:

  \Agda{Diffing/Universe/Syntax}{U-monster}

%format MCM = "\mathcal{M}"
 In Haskell, this type would be defined as |type MCM a = LTree a [a]|. The
existence of these non-intuitive types makes it extremely complicated, if not
impossible, to formally state properties relating the arity of an element and
the arity of its type, moreover, \CF does not differentiate between sums-of-products. 

  Fixing the type-unsafety we have in our model is not very difficult. By encoding our
algorithm in a kinded universe that more closely resemble Haskell types does the trick.
This is left as future work.
  
\section{Conclusion}
  \begin{itemize}
    \item This is what we take out of it.
  \end{itemize}
  
  %% WARNING: Do NOT change the next comment, it's a tag for sed to
  %% glue the bibliography.
  
  %%%!BIBHOOK!%%%
  

\end{document}
