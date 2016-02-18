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

\title{Best Title in the Universe}
\subtitle{42}

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
  The majority of version control systems handle patches in a non-structured
way. They see a file as a list of lines that can be inserted, deleted or
modified, with no regard to the semantics of that specific file. The immediate
consequence of such design decision is that we, humans, have to solve a large
number of conflicts that arise from, in fact, non conflicting edits.
Implementing a tool that knows the semantics of any file we happen to need,
however, is no simple task, specially given the plethora of file formats we see
nowadays. 
  
  This can be seen from a simple example. Lets imagine Alice and Bob are
iterating over a cake's recipe. They decide to use a version control system and
an online repository to keep track of their modifications.
  
\begin{figure}[h]
\begin{center}
\csvAOBlbl{\begin{tabular}{lll}
items & qty & unit \\
flour & 2    & cp  \\
eggs  & 2    & units 
\end{tabular}}{\begin{tabular}{lll}
items & qty & unit \\
flour & 1   & cp   \\
eggs  & 2   & units
\end{tabular}}{\begin{tabular}{lll}
items & qty & unit \\
cakeflour & 1   & cp \\
eggs  & 2   & units \\
sugar & 1   & tsp
\end{tabular}}{Alice}{Bob}
\end{center}
\caption{Sample CSV files}
\label{fig:csvfiles}
\end{figure}

  Lets say that both Bob and Alice are happy with their independent changes and
want to make a final recipe. The standard way to track differences between files
is the \sheltt{diff3} \mcite{diff3} unis tool. Running \sheltt{diff3 Alice.csv
O.csv Bob.csv} would result in the output presented in figure
\ref{fig:diff3output}. Every tag \sheltt{====} marks a difference. Three
locations follows, formatted as \sheltt{file:line type}. The change type can be
a \emph{Change}, \emph{Append} or \emph{Delete}. The first one, says that file 1
(\sheltt{Alice.csv}) has a change in line 2 (\sheltt{1:2c}) which is
\sheltt{flour, 2 , cp}; and files 2 and 3 have different changes in the same
line. The tag \sheltt{====3} indicates that there is a difference in file 3
only. Files 1 and 2 should append what changed in file 3 (line 4). 

\begin{figure}[h]
\begin{verbatim}
====
1:2c
  flour, 2  , cp  
2:2c
  flour, 1  , cp  
3:2c
  cakeflour, 1  , cp  
====3
1:3a
2:3a
3:4c
  sugar, 1  , tsp
\end{verbatim}
\caption{Output from \sheltt{diff3}}
\label{fig:diff3output}
\end{figure}

  If we try to merge the changes, \sheltt{diff3} will flag a conflict and
therefore require human interaction to solve it, as we can see by the presence
of the \sheltt{====} indicator in its output. However, Alice's and Bob's edits,
in figure \ref{fig:csvfiles} do \emph{not} conflict, if we take into account the
semantics of CSV files. Although there is an overlapping edit at line 1, the
fundamental editing unit is the cell, not the line.

  We propose a structural diff that is not only generic but also able to track
changes in a way that the user has the freedom to decide which is the
fundamental editing unit. Our work was inspired by \cite{Loh2009} and \cite{Vassena2015}. We did extensive changes in order to handle structural merging of patches. We also propose extensions to
this algorithm capable of detecting purely structural operations such as
refactorings and cloning. 
    
  The paper begins by exploring the problem, generically, in the Agda
\mcite{agda} language. Once we have a provably correct algorithm, the details of
a Haskell implementation of generic diff'ing are sketched. To open ground for
future work, we present a few extensions to our initial algorithm that could be
able to detect semantical operations such as \emph{cloning} and \emph{swapping}. 
  
\subsection*{Contributions}

\begin{itemize}
  \item We provide a type-indexed definition of a generic diff, over
        the universe of context-free types.
  \item We provide the base, proven to be correct, algorithms for computing
        and applying a diff generically.
  \item A notion of residual is used to propagate changes of different diffs,
        hence providing a bare mechanism for merging and conflict resolution.
  \item We provide a Haskell prototype with advanced, user defined, 
        automatic conflict solving strategies.
\end{itemize} 


\subsection*{Background}

\begin{TODO}
  \item Should we have this section? It cold be nice
        to at least mention the edit distance problem and that
        in the untyped scenario, the best running time is of $O(n^3)$.
        Types should allow us to bring this time lower.
\end{TODO}
  
\section{Structural Diffing}

  Alice and Bob were both editing a CSV file which represents data
that is isomorphic to |[[Atom String]]|, where |Atom a| is a simple tag that
indicates that |a|s should be treated abstractly, that is, either they are equal
or different, we will not open these values to check for structural changes.

  As we are tracking differences, there are a few operations that are inherent
to our domain, such as: inserting; deleting; copying and updating. When we say
\emph{structural diffing}, however, we add another option to this list. Now we
will also be able to go down the structure of some object and inspect its parts.
To illustrate this, let us take Alice's change as in figure \ref{fig:csvfiles},
her changes to the file could be described, structurally, as:

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
  
  \begin{TODO}
    \item connect this section and the next
  \end{TODO}
  
\newcommand{\CF}{\text{CF}}
\subsection{Context Free Datatypes}
\label{sec:cf}

  Although our running example, of CSV files, has type |[[String]]|,
lists of $a$ themselfes are in fact the least fixed point of the functor $X
\mapsto 1 + a \times X$. Which is a \emph{context-free type}, in the sense of
\cite{Altenkirch2006}. For it is constructed following the grammar $\CF$ of
context free types with a deBruijn representation for variables.
  
  \[
    \CF ::= 1 \mid 0 \mid \CF \times \CF \mid \CF + \CF \mid \mu \; \CF \mid \mathbb{N}
              \mid (\CF \; \CF)
  \]
  
  In Agda, the $\CF$ universe is defined by:
  
  \Agda{Diffing/Universe/Syntax}{U-def}
  
  Here, \IC{$\beta$} stands for type application; \IC{$vl$} is the topmost
variable in scope and \IC{$wk$} ignores the topmost variable in scope. We could
have used a \F{Fin} to identify variables, and have one instead of two constructors
for variables, but that would trigger more complicated definitions later on.
  
  We stress that one of the main objectives of this project is to release a 
solid diffing and merging tool, that can provide formal guarantees, written in Haskell.
The universe of user-defined Haskell types is smaller than context free types;
in fact, we have fixed-points of sums-of-products. Therefore, we should be able
to apply the knowledge acquired in Agda directly in Haskell. In fact, we did so!
With a few adaptations here and there, to make the type-checker happy, the
Haskell code is almost a direct translation, and will be discussed in section
\ref{sec:haskell}.
  
  Stating the language of our types is not enough. We need to specify its
elements too, after all, they are the domain which we seek to define our
algorithms for! Defining elements of fixed-point types make things a bit more
complicated, check \cite{Altenkirch2006} for a more in-depth explanation of
these details. Long story short, we have to use a decreasing \F{Tel}escope to
satisy the termination checker. In Agda, the elements of \F{U} are defined by:
  
  \Agda{Diffing/Universe/Syntax}{ElU-def}
  
  The \F{Tel} index is the telescope in which to look for the instantiation
of type-variables. A value $(v\; :\; \F{ElU}\; \{n\}\; ty\; t)$ reads roughly
as: a value of type $ty$ with $n$ variables, applied to $n$ types $t$ with at
most $n-1$ variables. We need this decrease of type variables to convince the
termination checker that our code is ok. It's Agda definition is:

  \Agda{Diffing/Universe/Syntax}{Tel-def}
  
  Let us see a simple example of how types and elements are defined in this
framework. Consider that we want to encode the list |(u : []) :: [U]|, for
|U| being the unit type with the single constructor |u|. We start by defining
the type of lists, this is an element of $\F{U}\;(\IC{suc}\;n)$, which later
lets us define an element of that type.

  \Agda{Diffing/Universe/Syntax}{U-example}
  
  So far so good. We seem to have the syntax figured out. But which operations
can we perform to these elements? As we shall see, this choice of universe
turns out to be very expressive, providing a plethora of interesting operations.
The first very usefull concept is the decidability of generic 
equality\cite{Altenkirch2006}.

  \Agda{Diffing/Universe/Equality}{equality-type}
  
  But only comparing things will not get us very far. We need to be able to
inspect our elements generically. Things like getting the list of immediate children,
or computing their arity, that is, how many children do they have, are very usefull.

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
a patch over $A$ to an object will produce a $Maybe\;T$. It is interesting
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

  For $T$ being the Unit type, we can not modify it.

  \Agda{Diffing/Patches/Diff/D}{D-void-def}
  
  For $T$ being a product, we need to provide \emph{diffs} for both
its components.

  \Agda{Diffing/Patches/Diff/D}{D-pair-def}
  
  For $T$ being a coproduct, things become slighlty more interesting. There
are four possible ways of modifying a coproduct, which are defined by:

  \Agda{Diffing/Patches/Diff/D}{D-sum-def}
  
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
  
  For types which are not fixed points, the \F{gdiff} functions looks like:
  
  \Agda{Diffing/Patches/Diff}{gdiff-def}
  
  Where the \F{gdiffL} takes care of handling fixed point values. The important
remark here is that it operates over lists of elements, instead of single
elements. This is due to the fact that the children of a fixed point element
is a (possibly empty) list of fixed point elements. 

\paragraph*{Fixed Points}

  have a fundamental difference over regular algebraic datatypes. They can grow
or shrink arbitralily. We have to account for that when tracking differences
between their elements. As we mentioned earlier, the diff of a fixed point is
defined by a list of \emph{edit operations}.
  
  \Agda{Diffing/Patches/Diff/D}{Dmu-type}
  
  Again, we have a constructor for adding \emph{extra} information, which is
ignored in the case of \F{Patches}.

  \Agda{Diffing/Patches/Diff/D}{Dmu-A-def}
  
  But the interesting bits are the \emph{edit operations} we allow,
where $\F{Val}\;a\;t = \F{ElU}\;a\;(\IC{tcons}\;\IC{u1}\;t)$:
  
  \Agda{Diffing/Patches/Diff/D}{Dmu-def}
  
  The reader familiar with \cite{Loh2009} will notice that they are almost the
same (adapted to our choice of universe), with two differences: 
our diff type is \emph{less type-safe}, which will be discussed in section \ref{sec:typesafety};
and instead of copying, we introduce a new constructor, \IC{D$\mu$-dwn}, which
is responsible for traversing down the type-structure. Copying is modelled by
$\IC{D$\mu$-dwn}\;(\F{gdiff-id}\; x)$. The intuition is that for every object
$x$ there is a diff that does not change $x$, we will look into this on
section \ref{sec:id}.
  
  Before we delve into diffing fixed point values, we need some specialization
of our generic operations for fixed points. Given that $\mu X . F\; X \approx
F\;1 \times [\mu X . F\; X]$, that is, any inhabitant of a fixed-point type can
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
We want to choose the diff with the least \emph{cost} between the three of them, for
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
should be the same patch. Proving they are actually equal is very tricky and
requires a lot of extra machinery regarding \F{$\_\lubmu\_$}, namelly it needs to
be associative and commutative. Moreover, inverses 
must distribute over it, that is $\F{D-inv}\;(p_a \F{$\lubmu$} p_b) =
\F{D-inv}\;p_a \F{$\lubmu$} \F{D-inv}\;p_b$. Note that the problem only arises when we are
evaluating $p_a \F{$\lubmu$} p_b$ for $p_a$ and $p_b$ with the same cost. 
  We do prove, however, that $\F{gdiff}\;y\;x$ and $\F{D-inv}\;(\F{gdiff}\;x\;y)$
behave on the same way. This means that for all practical purposes, they are indistinguishible.
We shall see what this statement means precisely in section \ref{sec:apply}.
  
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

  In order to achieve a meaningfull definition, we will impose that our \F{cost}
function must make the distance we defined above into a metric, that is:
  
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
that is not what we are looking for in a fine-tuned diff algorithm. Let us then define
$c_\oplus\;x\;y = \F{cost }(\IC{D-setr}\;x\;y) = \F{cost }(\IC{D-setl}\;x\;y)$ and
$c_\mu\;x = \F{cost }(\IC{D$\mu$-ins}\;x) = \F{cost }(\IC{D$\mu$-del}\;x)$ so we can
take this fine-tunning into account.

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
$c_\oplus$ and $c_\mu$. Let us then take a look at where the difference between
these values comes into play. Assume we have stoped execution of \F{gdiffL} at
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

  There is a catch here! Let us compare $d_1$ and $d_3$. By choosing $d_1$, we
would be opting to insert $hdY$ instead of transforming $hdX$ into $hdY$, this
is indeed preferable if we dont have to delete $hdX$ later on, in
$\F{gdiffL}\;(x \cons xs)\;(chY \cat ys)$, as that would be a waste of information. 
This wasteful scenario happens when $hdX \in chY \cat ys$. Now, assuming without loss
of generality that $hdX$ is the first element in $chY \cat ys$, we have that:
\[ d_1 = \DmuIns hdY \cons \DmuDel hdX \cons \F{tail}\;d_3 \]

  Hence, \F{cost }$d_1$ is $c_\mu\;hdX + c_\mu\;hdY + w$, for some $w \in \mathbb{N}$.
Since we want to apply this to Haskell datatypes by the end of the day, it is acceptable
to assume that $hdX$ and $hdY$ are values of the same finitary coproduct, representing
the constructors of the fixed-point datatype. If $hdX$ and $hdY$ comes from different 
constructors of our fixed-point datatype in question,
then $hdX = i_j\; x'$\footnote{
%%%% FOOTNOTE
We use $i_j$ to denote the $j$-th injection into a finitary coproduct. 
%%%% FOOTNOTE
} and $hdY = i_k\; y'$ where $j \neq k$. The patch from $hdX$ to $hdY$ will
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

Now is the time for assigning values to $c_\mu$ and $c_\oplus$ and the diffing
algorithm is completed. In fact, we define:

  \Agda{Diffing/Patches/Diff/Cost}{cost-def}
  
  Where $\F{costL} = sum \cdot map\; \F{cost$\mu$}$ and the size of an element is defined by:
  
  \Agda{Diffing/Universe/Measures}{sizeEl}

Note that there are an infinite amount of definitions that would fit here. This is
indeed a central topic of future work, as the \F{cost} function is what drives
the diffing algorithm. This is deceptively complicated, though. Since \F{$\_\lubmu\_$} is 
not commutative nor associative, in general, we do not have much room to reason
about the result of a \F{gdiffL}. A more careful definition of \F{$\_\lubmu\_$} that can provide
more properties is paramount for a more careful study of the \F{cost} function.
Defining \F{$\_\lubmu\_$} in such a way that it gives us a lattice over patches
and still respects patch inverses is very tricky. One option would be to aim for a 
quasi-metric $d$ instead of a metric (dropping equation (2)), this way inverses need not
to distribute over \F{$\_\lubmu\_$} and we can still define a metric $q$, but now with codomain $\mathbb{Q}$,
as $q\;x\;y = \frac{1}{2}(d\;x\;y - d\;y\;x)$.

\subsection{Applying Patches}
\label{sec:apply}

  At this stage we are able to: work generically on a suitable universe; describe
how elements of this universe can change and compute those changes. In order to
make our framework usefull, though, we need to be able to apply the patches we
compute. To our luck, the application of patches is easy, for we will only
show the implementation for coproducts and fixedpoints here. The rest is very
straight forward.

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

  The important part of application is that it must produce the 
expected result. A correctness result guarantees that. Its
proof is too big to be shown here, however, it has type:

  \Agda{Diffing/Postulated}{gdiff-correctness}
  
  Also relevant is the fact that the inverse of a patch behaves as it should:
  
  \Agda{Diffing/Patches/Diff/Inverse}{D-inv-sound-type}
  
  We have given algorithms for computing and applying differences over
elements of a generic datatype. Moreover, we proved our algorithms are correct
with respect to each other. This functionality is necessary for constructing
a version control system, but it is by no means sufficient!
   
\section{Patch Propagation}

  Let's say Bob and Alice perform edits in a given object, which are captured by
patches $p$ and $q$. In the version control setting, the natural question to ask
is \emph{how do we join these changes}.
  
  There are two solutions that could possibly arise from this question. Either
we group the changes made by $p$ and by $q$ (as long as they are compatible) and
create a new patch to be applied on the source object, or, we calculate how to
propagate the changes of $p$ over $q$ and vice-versa. Figure \ref{fig:residual}
illustrates these two options.
  
  \begin{figure}[h]
  \begin{displaymath}
    \xymatrix{
         & A_0 \ar[dl]_{p} \ar[dr]^{q} &  &
         & A_0 \ar[dl]_{p} \ar[dr]^{q} \ar[dd]_{p \cup q} & \\
         A_1 \ar[dr]_{q / p} & & A_2 \ar[dl]^{p / q} & 
         A_1 & & A_2 \\
         & A_3 & & & A_3 &     
      }
  \end{displaymath}
  \caption{Residual Square on the left; three-way-merging on the right}
  \label{fig:residual}
  \end{figure}
    
  The residual $p / q$ of two patches $p$ and $q$ only makes sense if both $p$
and $q$ are aligned, that is, are defined for the same input. It captures the
notion of incorporating the changes made by $p$ in an object that has already
been modified by $q$.
  
  We chose to use the residual notion, as it seems to have more structure into
it. Not to mention we could define $p \cup q \equiv (q \ p) \cdot p \equiv (p /
q) \cdot q$. Unfortunately, however, there exists conflicts we need to take care
of, which makes everything more complicated.
  
  In an ideal world, we would expect the residual function to have type |D a ->
D a -> Maybe (D a)|, where the partiality comes from receiving two non-aligned
patches.
  
  But what if Bob and Alice changes the same cell in their CSV file? Then it is
obvious that someone (human) have to chose which value to use in the final,
merged, version. 
  
  For this illustration, we will consider the conflicts that can arise from
propagating the changes Alice made over the changes already made by Bob, that
is, $p_{alice} / p_{bob}$.
  
  \begin{itemize}
    \item If Alice changes $a_1$ to $a_2$ and Bob changed $a_1$ to $a_3$,
          with $a_2 \neq a_3$, we have an \emph{update-update} conflict;
    \item If Alice adds information to a fixed-point, this is
          a \emph{grow-left} conflict;
    \item When Bob added information to a fixed-point, which Alice didn't,
          a \emph{grow-right} conflict arises;
    \item If both Alice and Bob add different information to a fixed-point,
          a \emph{grow-left-right} conflict arises;
    \item If Alice deletes information that was changed by Bob we have
          an \emph{delete-update} conflict;
    \item Last but not least, if Alice changes information that was deleted by Bob
          we have an \emph{update-delete} conflict.          
  \end{itemize}
  
  Above we see two distinct conflict types. An \emph{update-update}
  conflict has to happen on a coproduct type, whereas the rest
  are restricted to fixed-point types. In Agda,
  
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

  The type of our residual\footnote{Our residual operation does not form a
residual as in the Term Rewriting System sense\cite{Bezem2003}. It might,
however, satisfy interesting properties. This is left as future work for now}.
operation is:
  
  \Agda{Diffing/Patches/Residual}{residual-type}
  
  We reitarate that the partiality comes from the fact the residual is not
defined for non-aligned patches. We chose to make a partial function instead of
receiving a proof of alignment purely for pratical purposes. Defining alignment
for our patches is very complicated.
  
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
Therefore, $merge_1\;m : \DCtty \xrightarrow{\mu_D \cdot D\; m} \Patchtty$ is the \emph{merge tool}
for removing the conflicts of a single patch.

  Even though the last paragraph was a simple informal sketch, as we did not have
enough time to figure out precisely how to fit our framework in theory, we can
see how solving conflicts is just a matter of walking over the patch structure and
removing them, one by one. This is unsurprising, and is exactly what we currently do manually
when merge conflicts arise on any mature version control system. The interesting bit, however, is
that different ways of walking the patch might give us more or less information
to handle a conflict. This opens up room for interesting automatic solvers, and
besides not having a formal theory (yet!), they've shown to be very promissing
in practice as we will illustrate in section \ref{sec:haskell}.

\subsection{A remark on Type Safety}
\label{sec:typesafety}

  There is one minor problem in our approach so far. Our \F{D$\mu$} type
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
run into a very subtle problem. In short, we can not prove that is two elements
come from the same constructor, they have the same arity. This hinders
\F{D$\mu$-dwn} useless. To fix this, we need to add kinds to our universe. Type
aplication does not behave the same way as in Haskell. Consider \F{list} as
defined in section \ref{sec:cf} and \F{ltree} as defined below.

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
algorithm in a kinded universe that more closely resemble Haskell types should do the trick.
This is left as future work. 
  
\section{A Category of Patches}

  \begin{TODO}
    \item Having patch composition and inversion we can design
          a version control system for a single file in a categorical setting.
          \begin{itemize}
            \item Label each composition chain as a branch,
                  let residuals do the merging after conflict resolution.
          \end{itemize}
  \end{TODO}

\begin{RESEARCH}
  \item Define patch composition, prove it makes a category.
  \item But then... does it make sense to compute the composition of patches?
  \item In a vcs setting, we always have the intermediate files that originated
        the patches, meaning that composition can be defined semantically
        by: $apply (p \cdot q) \equiv apply q \circ apply p$, where $\circ$ is
        the Kleisli composition of $+1$.
  \item This gives me an immediate category... how usefull is it?
\end{RESEARCH}
  
\section{A Haskell Prototype}
\label{sec:haskell}
  
\subsection{The Interface}

  \begin{TODO}
    \item present the |Diffable| typeclass.
  \end{TODO}

\subsection{Sums-of-Products and Fixed points}

  \begin{TODO}
    \item present the |HasAlg| and |HasSOP| classes.
    \item mention the memoization table for diffing fixed points.
  \end{TODO}

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
  
\section{Related Work}
  
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
  
\section{Conclusion}
  \begin{itemize}
    \item This is what we take out of it.
  \end{itemize}
  
  %% WARNING: Do NOT change the next comment, it's a tag for sed to
  %% glue the bibliography.
  
  %%%!BIBHOOK!%%%
  

\end{document}
