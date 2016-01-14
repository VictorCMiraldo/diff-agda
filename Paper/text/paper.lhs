\documentclass{sigplanconf}
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

\newcommand{\warnme}[1]{{\color{red} \textbf{$[$} #1 \textbf{$]$}}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Agda related stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% empty env, maybe later we can add some style to it.
\newenvironment{agdacode}{%
\vspace{.5em}
\hspace{1em}
\begin{minipage}[t]{.8\textwidth}
}{%
\end{minipage}
\vspace{.5em}
}

\newcommand{\Agda}[2]{%
\begin{agdacode}
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

%%%%%%

\newcommand{\sheltt}[1]{\texttt{\small #1}}

%%%%%%
%% Definitions and lemmas

\newtheorem{definition}{Definition}[section]

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
fundamental editing unit. Our work is built on top of \mcite{loh2009}, but we
extend it in order to handle merging of patches. We also propose extensions to
this algorithm capable of detecting purely structural operations such as
swapping and cloning. 
    
  The paper begins by exploring the problem, generically, in the Agda
\mcite{agda} language. Once we have a provably correct algorithm, the details of
a Haskell implementation of generic diff'ing are sketched. To open ground for
future work, we present a few extensions to our initial algorithm that could be
able to detect semantical operations such as \emph{cloning} and \emph{swapping}. 
  
\subsection*{Contributions}

\subsection*{Background}

\begin{TODO}
  \item Should we have this section? It cold be nice
        to at least mention the edit distance problem and that
        in the untyped scenario, the best running time is of $O(n^3)$.
        Types should allow us to bring this time lower.
\end{TODO}
  
\section{Structural Diffing}

  Alice and Bob were both editing a CSV file which represents data
  that is isomorphic to |[[Atom String]]|, where |Atom a| is a simple
  tag that indicates that |a|s should be treated as atomic. 
  
  \begin{TODO}
    \item What do we mean by structural?
    \item Give some context: Tree-edit distance; 
    \item We seek to obtain a system with something close to residuals.
  \end{TODO}
  
  \begin{RESEARCH}
    \item Check out the antidiagonal with more attention: 
          \url{ http://blog.sigfpe.com/2007/09/type-of-distinct-pairs.html }
    \item The LCS problem is closely related to diffing.
          We want to preserve the LCS of two structures!
          How does our diffing relate?
          Does this imply maximum sharing?
  \end{RESEARCH}
  
\subsection{Context Free Datatypes}
  
  \begin{TODO}
    \item Explain the universe we're using.
    \item Explain the intuition behing our $D$ datatype.
    \item Mention that it is correct.
  \end{TODO}
  
  \Agda{Diffing/Universe/Syntax}{U-def}
  
  \begin{TODO}
    \item Explain the patching problem.
    \item We want a type-safe approach.
    \item Argue that the types resulting from our parser
          are in a sub-language of what we treated next.
    \item introduce \emph{edit-script}, \emph{diffing} and \emph{patching} or \emph{apply}
  \end{TODO}
  
\subsection{Patches over a Context Free Type}

  \begin{TODO}
    \item Explain that a patch is something which we can apply.
    \item Loh's approach is too generic, as the diff function
          should have type $a \rightarrow a \rightarrow D\; a$.
  \end{TODO}

  In order to simplify the presentation, we are gonna explicitely name variables
and write our types in a more mathematical fashion, other than the Agda
encoding. As we discussed earlier, a patch is an object that track differences
in a given type. Different types will allow for different types of changes.
  
  \begin{definition}[Simple Patch]
  We define a (simple) patch $D\; ty$ by induction on $ty$ as:
    \begin{eqnarray*}
      D\; 0 & = & 0 \\
      D\; 1 & = & 1 \\
      D\; (x \times y) & = & D\; x \times D\; y \\
      D\; (x + y) & = & (D\; x + D\; y) + 2\times(x \times y) \\
      D\; (\mu X . F\; X) & = & \mu X . (1 \\
                          & + & D\;(F\;1) \times X \\
                          & + & 2\times(F\;1) \times X \\
                          & ) & 
    \end{eqnarray*}
  \end{definition}
  
  Let's see the coproduct case in more detail. There are four different
possibilities for the changes seen in a coproduct, just like there are four
different combinations of constructors for two objects of type |Either a b|. The
first and second options, namelly $D\; x$ and $D\; y$ track differences of a
|Left a| into a |Left a'| and a |Right b| into a |Right b'|, respectively. The
other possibilities are representing a |Left a| becoming a |Right b| or
vice-versa. The other branches are straight-forward.
  
  \begin{definition}[Defined]
    We say that a patch $p_a$ is defined for an input $a$ iff there
    exists an object $a'$ such that:
    
    \[ \text{apply }p_a\;a \equiv \text{Just }a' \]
  \end{definition}
  
\paragraph*{Fixed Points}

  \begin{TODO}
    \item Very close to Vassena's and Andres approach;
    \item Explicit grow conflicts.
    \item Maybe we should also consider deletes as shrink conflicts?
  \end{TODO}

\subsection{Sharing of Recursive Subterms}

  \begin{itemize}
    \item If we want to be able to share recursive subexpressions
          we need a mutually recursive approach.
  \end{itemize}
  
\subsection{Remarks on Type Safety}

  \begin{itemize}
    \item At which level of our design space we would like type-safety?
    \item Maybe after introducing the matrix idea it is clear that
          type-safety might be desirable only on the diff level, not on the patch level.
  \end{itemize}
  
\section{Residuals}

  Let's say Bob and Alice perform edits in a given object, which
  are captured by patches $p$ and $q$, shown in figure \ref{fig:residual}.
  The natural question to ask is \emph{how do we join these changes}.
  
  \begin{figure}[h]
  \begin{displaymath}
    \xymatrix{
         & A_0 \ar[dl]_{p} \ar[dr]^{q} & \\
         A_1 \ar[dr]_{q / p} & & A_2 \ar[dl]^{p / q} \\
         & A_3 &      
      }
  \end{displaymath}
  \caption{Residual Square}
  \label{fig:residual}
  \end{figure}
  
  The residual $p / q$ of two patches $p$ and $q$ only makes sense if
  both $p$ and $q$ are aligned, that is, are defined for the same input.
  It captures the notion of incorporating the changes made by $p$ in
  an object that has already been modified by $q$.
  
  \begin{TODO}
    \item Pijul has this notion of handling a merge as a pushout,
          but it uses the free co-completion of a rather simple category.
          This doesn't give enough information for structured
          conflict solving.
    \item BACK THIS UP!
  \end{TODO}
  
  In an ideal world, we would expect the residual function
  to have type |D a -> D a -> Maybe (D a)|, where the partiality
  comes from receiving two non-aligned patches.
  
  But what if Bob and Alice changes the same cell in their CSV file?
  Then it is obvious that someone (human) have to chose which value to
  use in the final, merged, version. 
  
  Here we see that this residual operation is where conflicts are introduced in
our theory.
  
\subsection{Incorporating Conflicts}

  In order to track down these conflicts we need a more expressive patch data
structure. We chose to parametrize $D$ over an abstract type and add another
dummy constructor to it, much like we would do in a free monad construction.
The actual data structure we use is presented in figure \ref{fig:ddef}.

  \begin{TODO}
    \item Show where conflicts arise and the two types
          of conflicts we identify.
  \end{TODO}
  
  \begin{figure*}
  \Agda{Diffing/Patches/Diff}{D-def}
  \caption{Complete Definition of $D$} 
  \label{fig:ddef}
  \end{figure*}
  
  Note that the first constructor of $D$ just asks for a suitably indexed $A$.
  With this in mind, we can now start to define our residual operation.
  
  \begin{TODO}
    \item Define $Patch = D\;\bot$
  \end{TODO}
  \Agda{Diffing/Patches/Residual}{residual-type}
  
  It is interesting to note that this residual operation is somewhat symmetric:
  
  \Agda{Diffing/Patches/Residual/Symmetry}{residual-symmetry-type}
  
  \Agda{Diffing/Patches/Residual/SymmetryConflict}{residual-sym-stable-type}
  
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
  


\section{Sketching a Control Version System}

  \begin{itemize}
    \item Different views over the same datatype will give different diffs.
    \item |newtype| annotations can provide a gread bunch of control over the algorithm.
    \item Directories are just rosetrees...
  \end{itemize}
  
\section{Related Work}
  \begin{itemize}
    \item People have done similar things... or not.
  \end{itemize}
  
\section{Conclusion}
  \begin{itemize}
    \item This is what we take out of it.
  \end{itemize}
  
  %% WARNING: Do NOT change the next comment, it's a tag for sed.
  
  %%% THEBIBLIOGRAPHYGOESHERE %%%

\end{document}
