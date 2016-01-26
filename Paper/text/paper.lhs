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

% Default code, no additional formatting.
\newcommand{\Agda}[2]{%
\begin{agdacode}
\ExecuteMetaData[excerpts/#1.tex]{#2}
\end{agdacode}
}

% Allows us to specify how much \hskip we want through #3.
\newcommand{\AgdaI}[3]{%
\begin{agdacode}[#3]
\ExecuteMetaData[excerpts/#1.tex]{#2}
\end{agdacode}
}

%% Agda shortcuts
\newcommand{\D}[1]{\AgdaDatatype{#1}}
\newcommand{\F}[1]{\AgdaFunction{#1}}
\newcommand{\K}[1]{\AgdaKeyword{#1}}
\newcommand{\N}[1]{\AgdaSymbol{#1}}
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

\begin{TODO}
  \item Study of a more algebraic patch theory.
  \item Agda model.
  \item Haskell Prototype.
\end{TODO}

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

  Although our running example, of CSV files, has type |[[Atom String]]|,
lists of $a$ themselfes are in fact the least fixed point of the functor $X
\mapsto 1 + a \times X$. Which is a \emph{context-free type}, in the sense of
\cite{Altenkirch2006}. For it is constructed following the grammar $\CF$ of
context free types with a deBruijn representation for variables.
  
  \[
    \CF ::= 1 \mid 0 \mid \CF \times \CF \mid \CF + \CF \mid \mu \; \CF \mid \mathbb{N}
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

  \Agda{Diffing/Patches/Diff}{D-type}
  
  As we mentioned earlier, we are interested in analizing the set of possible
changes that can be made to objects of a type $T$. These changes depend on
the structure of $T$, for the definition follows by induction on it.

  For $T$ being the Unit type, we can not modify it.

  \Agda{Diffing/Patches/Diff}{D-void-def}
  
  For $T$ being a product, we need to provide \emph{diffs} for both
its components.

  \Agda{Diffing/Patches/Diff}{D-pair-def}
  
  For $T$ being a coproduct, things become slighlty more interesting. There
are four possible ways of modifying a coproduct, which are defined by:

  \Agda{Diffing/Patches/Diff}{D-sum-def}
  
  We also need some housekeeping definitions to make sure we handle all
types defined by \F{U}.

  \Agda{Diffing/Patches/Diff}{D-rest-def}
  
  Fixed points are handled by a list of \emph{edit operations}. We will
discuss them in detail later on.

  \Agda{Diffing/Patches/Diff}{D-mu-def}
  
  The aforementioned parameter $A$ goes is used in a single consrtuctor,
allowing us to have a free-monad structure over \F{D}'s. This shows to be
very usefull for adding extra information, as we shall discuss, on section 
\ref{sec:conflicts}, for adding conflicts.

  \Agda{Diffing/Patches/Diff}{D-A-def} 
 
  Finally, we define $\F{Patch}\;t\;ty$ as $\F{D}\;(\lambda \;\_\;\_ \rightarrow \bot)\; t\; ty$.
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
  
  Here the \F{gdiffL} function is very close to what was shown in
\cite{Loh2009}, with a slight modification.

\paragraph*{Fixed Points}

  have a fundamental difference over regular algebraic datatypes.
  They can grow or shrink arbitralily. We have to account for that when
  tracking differences between their elements. As we mentioned earlier,
  the diff of a fixed point is defined by a list of \emph{edit operations}.
  
  \Agda{Diffing/Patches/Diff}{Dmu-type}
  
  Again, we have a constructor for adding \emph{extra} information, which is
ignored in the case of \F{Patches}/

  \Agda{Diffing/Patches/Diff}{Dmu-A-def}
  
  But the interesting part, for now, are the \emph{edit operations} we allow.
  
  \Agda{Diffing/Patches/Diff}{Dmu-def}
  
  The reader familiar with \cite{Loh2009} will notice that they are almost the same
(adapted to our choice of universe), with the exception of the \IC{D$\mu$-dwn} constructor.
  
  
  it is straight forward to see that the $D\; (\mu X . F\; X)$ is isomorphic to
a list with three recursive constructors and a non-recursive one. Following the
edit operations studied by L\"{o}h\cite{loh2009}, we have an \emph{insert}, a
\emph{delete} and a \emph{end} edit operations. The big difference is that
instead of copying, we have a constructor that track changes inside a
constructor of $\mu X . F \; X$, we call this a \emph{down} edit operation.

  We heavily rely on the facth that $\mu X . F\; X \approx F\;1 \times [\mu X . F\; X]$,
  that is, any inhabitant of a fixed-point type can be seen as a non-recursive head
  and a list of recursive children, or, expressed in our generic setting:
  
  \Agda{Diffing/Universe/MuUtils}{Openmu-def}
  
  \Agda{Diffing/Universe/MuUtils}{mu-open-type}
  
  \Agda{Diffing/Universe/MuUtils}{mu-close-type}
  
  Although we could have used vectors of a fixed length and made this a total
  isomorphism, we would have more problems than benefits. This will be discussed
  in section \ref{subsec:typesafety}. Nonetheless, an important soundness result
  has been proven:
  
  \Agda{Diffing/Universe/MuUtils}{mu-close-resp-arity-lemma}
  
\subsection{The Cost Function}

  \begin{TODO}
    \item the cost function should satisfy a few properties, such as:
          if $x$ and $y$ come from the same constructor,
          then $cost (diff x y) \le cost (Del x :: Add y :: End)$.
          Otherwise, $gdiffL$ will always choose $DmuDwn$ first.
  \end{TODO}

\section{A Category of Patches}

\begin{RESEARCH}
  \item Define patch composition, prove it makes a category.
  \item But then... does it make sense to compute the composition of patches?
  \item In a vcs setting, we always have the intermediate files that originated
        the patches, meaning that composition can be defined semantically
        by: $apply (p \cdot q) \equiv apply q \circ apply p$, where $\circ$ is
        the Kleisli composition of $+1$.
  \item This gives me an immediate category... how usefull is it?
\end{RESEARCH}
  
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
  
  Here \F{$<M>$} denotes the Kleisli composition of the $Maybe$ monad and
  \F{$\downarrow-map-\downarrow$} takes care of the indexes.
    
  Now, we can compute both $p / q$ and $q / p$ at the same time. It also
backs the intuition that using residuals or patch commutation (as in darcs) is
not significantly different.
  
  This means that $p / q$ and $q / p$, although different, have the same conflicts
(up to symmetry).
  
\subsection{Solving Conflicts}

  \begin{TODO}
    \item This is highly dependent on the structure.
    \begin{itemize}
      \item some structures might allow permutations,
            refactorings, etc... whereas others might not.
    \end{itemize}
    \item How do we go generic? Free-monads to the rescue!
  \end{TODO}
  
\section{Summary and Remarks}

\subsection{Sharing of Recursive Subterms}

  \begin{itemize}
    \item If we want to be able to share recursive subexpressions
          we need a mutually recursive approach.
    \item Or, this will be handled during conflict solving. See refactoring.
  \end{itemize}
  
\subsection{Remarks on Type Safety}
\label{subsec:typesafety}

  \begin{itemize}
    \item only the interface to the user can be type-safe,
          otherwise we don't have our free-monad multiplication.
  \end{itemize}
  
\section{A Haskell Prototype}
\label{sec:haskell}
  
  \begin{TODO}
    \item throw \emph{hs-diff} in github before the deadline!
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
