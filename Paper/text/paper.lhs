\documentclass{sigplanconf}
\usepackage[english]{babel}
\usepackage{savesym}
\usepackage{amsmath}
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
    \item Give some context: Tree-edit distance; 
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
  \end{TODO} 

  Having a regular, yet extensible, way to parse different files gives us a stepping
  stone to start discussing how to track differences in the results of those parsers.
  There has been plenty of research on this topic (\warnme{CITE STUFF!}), however,
  most of the time data is converted to an untyped intermediate representation.
  We would like to stay type-safe. \warnme{WHY?}  
  Our research shows that the type |D a| that expresses the differences between
  two elements of type |a| can be determined by induction on |a|'s structure.
  
  \begin{TODO} 
    \item introduce \emph{edit-script}, \emph{diffing} and \emph{patching} or \emph{apply}
  \end{TODO}
  
  For example, let us see the differences between the original CSV and Alice's edits: 
  
  \begin{figure}[h]
  \begin{center}
  \begin{minipage}[t]{.3\textwidth}
  \begin{verbatim}
items      ,qty ,unit
wheat-flour,2   ,cp
eggs       ,2   ,units
  \end{verbatim}
  \begin{center}Alice\end{center}
  \end{minipage}
  \vline
  \begin{minipage}[t]{.3\textwidth}
    \begin{verbatim}
items      ,qty ,unit
wheat-flour,1   ,cp
eggs       ,2   ,units
  \end{verbatim}
  \begin{center}Original\end{center}
  \end{minipage}
  \end{center}
  \caption{Alice's edits}
  \label{fig:aliceedit}
  \end{figure}
  
  \begin{wrapfigure}{r}{.4\textwidth}
  \begin{code}
    Cpy "items,qty,unit" 
      (Del "weat-flour,1,cp" 
        (Ins "wheat-flour,2,cp" 
          (Cpy "eggs,2,unis"
            End)))
  \end{code}
  \caption{Line-based edit-script for figure \ref{fig:aliceedit}}
  \label{fig:line-based-ES}
  \end{wrapfigure}
  
  As we can see, Alice edited the second line of the file. A line-based edit script,
  which is something that transform a file into another, would look like the one
  presented in figure \ref{fig:line-based-ES}. That edit script has a few problems:
  (A) it is deleting and inserting almost identical lines and (B) it is unaware
  of the CSV file semantics, making it harder to identify actual conflicts.

\section{Sharing of Recursive Subterms}

  \begin{itemize}
    \item If we want to be able to share recursive subexpressions
          we need a mutually recursive approach.
  \end{itemize}
  
\section{Remarks on Type Safety}

  \begin{itemize}
    \item At which level of our design space we would like type-safety?
    \item Maybe after introducing the matrix idea it is clear that
          type-safety might be desirable only on the diff level, not on the patch level.
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
