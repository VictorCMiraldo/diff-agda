\documentclass{llncs}
\usepackage[english]{babel}
\usepackage{savesym}
\usepackage{amsmath}
\usepackage{wrapfig}
\usepackage{catchfilebetweentags}
\usepackage{agda}

\newenvironment{TODO}{%
  \color{blue} \itshape \begin{itemize}
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
\newcommand{\textmu}{$\mu$}
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

\title{Best Title in the Universe}

\author{Victor Cacciari Miraldo}

%include lhs2TeX.fmt

\begin{document}
\maketitle

\begin{abstract}
stuff
\end{abstract}

\section{Introduction}
  The majority of version control systems handle patches in a non-structured way. They see
  a file as a list of lines that can be inserted, deleted or modified, with no regard to
  the semantics of that specific file. The immediate consequence of such design decision
  is that we, humans, have to solve a large number of conflicts that arise from, in fact,
  no conflicting edits, yet, the tools fail to see such edits as non-conflicting as they
  are not aware of the file's semantics. Implementing a tool that knows the semantics 
  of any file we happen to need, however, is clearly not an easy task, specially given the 
  plethora of file formats we see nowadays. 
  
  Let us illustrate this with the following three CSV files:
  
  \begin{TODO}
    \item show three different CSV files that conflict under diff3.
  \end{TODO}
  
  It is not hard to see that Alice's and Bob's edits do \emph{not} conflict. However,
  the diff3 \warnme{cite!} tool will flag them as such. On this paper we address 
  two problems: (A) how to parse things generically and (B) how to diff over the results
  of these parsers and merge them properly.
  
  To summarize our contributions,
  \begin{itemize}
    \item We present a generic parsing and pretty printing library built on Haskell's type-level,
          using a similar technique as in \cite{Loh2015}.
    \item We model the notion of \emph{patch} generically, and prove it's correctness.
  \end{itemize}  

\section{Type Level Parser Combinators}

  \begin{wrapfigure}{r}{.3\textwidth}
  \begin{eqnarray*}
    CSV & ::= & (line\; '\backslash n')* \\
    line & ::= & string \\
         & || & string\; ','\;line
  \end{eqnarray*}
  \caption{CSV grammar}
  \label{fig:csvgrammar}
  \end{wrapfigure}

  Sticking to CSV as our \emph{to-go} example, we can write its grammar in BNF as
  showed in figure \ref{fig:csvgrammar}, it can be read as \emph{A CSV file consists
  in many lines, where many lines consists in a list of strings separated by commas}.
  From this description, it is already expected that a CSV parser will return
  a $[ [ String ] ]$, given an input file in the CSV format. But the converse should also
  be easy! Given a $[ [ String ] ]$, knowing that it represents a CSV file, we should
  be able to print it as such.
  
  Our parser combinator library works just like that. We encode the grammar of a language
  on Haskell's type-level, making it possible to generate the parser from different instances.
  The parser for CSV would be written as:
  
\vskip 1em
\begin{code}
  type CSVParser = VMany (HSepBy Iden (Sym ","))  
\end{code}
\vskip 1em

  \warnme{Find a name for our library!}
  \begin{TODO}
    \item Explain a few of our combinators. Some emphasis on $:<\$>$.
    \item Describe hoe different combinators might have the same
          parsing behaviour but not the same pretty printing behaviour.
          Example: $VMany$ vs $HMany$.
    \item Show the $HasParser$ class.
    \item Explain how do we handle mutually recursive types.
  \end{TODO}
  
\section{Diffing the results}
  \begin{TODO}
    \item Explain the patching problem.
    \item We want a type-safe approach.
    \item Argue that the types resulting from our parser
          are in a sub-language of what we treated next.
  \end{TODO}  

\section{Context Free Datatypes}
  
  \begin{TODO}
    \item Explain the universe we're using.
    \item Explain the intuition behing our $D$ datatype.
    \item Mention that it is correct.
  \end{TODO}
  
  \Agda{Diffing/Universe/Syntax}{U-def}
  
\section{Related Work}
  \begin{itemize}
    \item People have done similar things... or not.
  \end{itemize}
  
\section{Conclusion}
  \begin{itemize}
    \item This is what we take out of it.
  \end{itemize}

\end{document}
