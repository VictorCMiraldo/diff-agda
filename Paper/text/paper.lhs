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
  the diff3 \warnme{cite!} tool will flag them as such. Using generic programming techniques
  we can do a better job at identifying actual conflicts. The problem is twofold, however: 
  (A) how to parse things generically and (B) how to diff over the results
  of these parsers and merge them properly.
  
  We begin by explaining how we can write parsers in a very generic fashion, using type-level
  \emph{grammar combinators}. This approach has lots of advantages, for instance, 
  it is easily invertible to generate pretty-printers. The exposition of our 
  library is guided by writing a CSV parser as an example. 
  
  Once we can solve the parsing problem in an elegant fashion, we address the diffing problem.
  Namelly, how can we take two values returned by a \emph{grammar} parser and represent
  the differences between them. 
  
  To summarize our contributions,
  \begin{itemize}
    \item We present a generic parsing and pretty printing library built on Haskell's type-level,
          using a similar technique as in \cite{Loh2015}.
    \item We model the notion of \emph{patch} generically, and prove it's correctness in Agda.
  \end{itemize}  

\section{Grammar Combinators}

  Our parser combinator library seeks to generate a parser and a pretty printer from
  the same specification. It is similar to \cite{Shaw2014} and \cite{Rendel2010} in its
  idea, but drastically different in implementation. We achieve our generic parsers
  by encoding our combinators on the type-level, then having differnt instances
  of a class |HasParser| for each of them. We were inpired by \cite{Loh2015}, who
  first used this technique to build API-driven web servers.
  
  Sticking to CSV as our \emph{to-go} example, we can write its grammar in BNF as
  shown in figure \ref{fig:csvgrammar}, it can be read as \emph{A CSV file consists
  in many lines}. From this description, it is already expected that a CSV parser will return
  a $[ Line ]$, given an input file in the CSV format. But the converse should also
  be easy! Given a $[ Line ]$, knowing that it represents a CSV file, we should
  be able to print it as such.

  \begin{wrapfigure}{r}{.4\textwidth}
  \begin{eqnarray*}
    CSV & ::= & (line\; '\backslash n')^* \\
    line & ::= & string \\
         &  || & string\;','\;line
  \end{eqnarray*}
  \caption{CSV grammar}
  \label{fig:csvgrammar}
  \vskip -0.5cm
  \end{wrapfigure}
  
  The idea here lies in the fact that a BNF already looks like a Haskell type declaration, and at the
  same time, acts as the \emph{type} of a language. We want to have (empty) types
  that mimick the BNF syntax and allow us to define instances by induction on their
  structure. The CSV grammar gives us the following datatype.
  
\vskip .5em
\begin{code}
    type CSV   = [ Line ]
    data Line  =  One   String
               |  More  String Line
\end{code}
\vskip .5em

\newcommand{\LRseq}{:\hskip -0.5mm < \hskip -2mm * \hskip -2mm >}
\newcommand{\Lseq}{:\hskip -0.5mm < \hskip -2mm * }
\newcommand{\Rseq}{:\hskip -0.5mm * \hskip -2mm >}
\newcommand{\LRchoice}{:\hskip -0.5mm < \mid >}
\newcommand{\LRapp}{:\hskip -0.5mm < \hskip -1mm \$ \hskip -1mm >}
\newcommand{\LRbang}{:\hskip -0.5mm < ! \hskip -1mm >}

%format :<*> = "\LRseq"
%format :<*  = "\Lseq"
%format :*>  = "\Rseq"
%format :<|> = "\LRchoice"
%format :<$> = "\LRapp"
%format :<!> = "\LRbang"
  
  Our parser combinators follow the applicative style, with some precedences swapped. 
  With least precedense we have |a :<*> b|, which will parse |a| then |b|, in sequence, and
  return |(Result a , Result b)|. Together with its forgetfull versions |a :*> b| and |a :<* b|, 
  wich will ignore the result from the left, or right, respectively. These type combinators are right associative.
  Then we have the choice combinator |a :<||> b|, which will try to parse |a|. If it fails,
  it proceeds by trying |b|, its result is |Either (Result a) (Result b)|. 
  And last we have a \emph{tagging} combinator |k :<$> a|
  which injects the result of |a| into a datatype |k|. We will explain this combinator
  in more detail in section \ref{subsec:application}.
  We stress that a exhaustive description of the grammar combinators is beyond the
  scope of this paper. We refer the reader to the hackage documentation {\color{red} PUT IT ONLINE!}
  for that.
  
  A few high level combinators are also available, for example |VMany a| and |HMany a|. 
  The parsing behaviour of both is the same, they will parse as many |a| s as possible.
  On the pretty-printing side, however, one will concat it's arguments vertically
  whereas the other will concat it's arguments horizontally.
  
  Henceforth, the CSV grammar written using our combinators looks like figure \ref{fig:csv-parser}.
  
\vskip .5em
\begin{figure}[h]
\begin{code}
    type CSVParser   = VMany LineParser
    
    type LineParser  = Line  :<$>  Iden
                             :<|>  Iden :<*> Sym "," :*> LineParser
                             
    csvParser :: Parser (Result CSVParser)
    csvParser = genParser (Proxy :: Proxy CSVParser)
\end{code} % $
\caption{CSV Parser}
\label{fig:csv-parser}
\end{figure}
\vskip .5em

  Using \texttt{-XDataKinds} GHC extension we can have type-level strings, which
  are suitable for defining combinators such as |Sym ","|, that parses the symbol |","|.
  Here, |genParser| and |Result| are definitions provided by the class |HasParser|,
  which is defined for all grammar combinators,
  
\vskip .5em
\begin{code}
class HasParser a where
  type Result a   :: *  
  genParser       :: Proxy a -> Parser (Result a)
\end{code}
\vskip .5em

  And, for illustration purposes, the instance for |VMany| is defined as:
  
\vskip .5em
\begin{code}
instance (HasParser a) => HasParser (VMany a) where
  type Result (VMany a) = [Result a]  
  genParser _ = many (genParser (Proxy :: Proxy a))
\end{code}
\vskip .5em

  Note that we need to keep using these proxies (from \texttt{Data.Proxy}) around
  so GHC can choose the correct instance to fetch |genParser| from. 
  
  The attentive reader might have noticed a few problems with the CSV parser presented
  in figure \ref{fig:csv-parser}. If we try to compile that code GHC will complain about
  a recursive type synonym. That is very easy to fix, however. We just wrap the recursive
  calls in a newtype and provide a cannonical instance\footnote{
%%%%%% BEGIN FOOTNOTE
In fact, we provide Template Haskell code to do exactly that. The user should just call
|$(deriveRec ''LineParser ''LineParserA)|.
%%%%%% END FOOTNOTE
  } for it.

\vskip .5em
\begin{code} 
    type LineParserA  = Line  :<$>  Iden
                              :<|>  Iden :<*> Sym "," :*> LineParser
    newtype LineParser = LP LineParserA
    
    instance HasParser LineParser where
      type Result LineParser = Result LineParserA
      genParser _ = genParser (Proxy :: Proxy LineParserA)
\end{code} % $
\vskip .5em

\subsection{The Tagging Combinator}
\label{subsec:application}

  Tagging is the least intuitive of the combinators, for it deserves its own section.
  The reason for including it in the library is to provide the user with a way
  to generate hiw own datatypes instead of standard\footnote{
%%%%% BEGIN FOOTNOTE
We call standard types any type built using |()| , |Either| , |(,)| , |[]| and
atomic types such as |Integer|, |String|, |Double|, ...
%%%%% END FOOTNOTE
  } ones. The important observation is
  that any Haskell type is isomorphic to a sum-of-products, which can be expressed
  using standard types. 
  
  The parser instance for |a :<$> b| is defined as:
\vskip .5em
\begin{code}
  instance (HasParser a , HasIso k (Result a)) => HasParser (k :<$> a) where
    type Result (k :<$> a) = k  
    genParser _ = genParser (P a) >>= return . og
\end{code} % $
\vskip .5em
  
  Where the |HasIso a b| class defines two functions |go :: a -> b| and |og :: b -> a|
  to convert values from one type to another. In our CSV example, we have the following
  instance:
  
\vskip .5em
\begin{code}
  instance HasIso Line (Either String (String , Line)) where
    go (One s)          = Left s
    go (More s l)       = Right (s , l)
    
    og (Right (s , l))  = More s l
    og (Left s)         = Left s
\end{code}
\vskip .5em

  The calculation below shows that |LineParser| indeed has the expected result type.
  Here we use |a ~ b| to denote an isomorphism between |a| and |b| meaning
  that we parse a value of type |b| and inject it into something of type |a| 
  through |og :: b -> a|.
  
  \begin{eqnarray*}
    |Result LineParser| & = & |Line ~ Result (Iden :<||> Iden :<*> Sym "," :*> LineParser)| \\
                        & = & |Line ~ Either (Result Iden) (Result (Iden :<*> Sym "," :*> LineParser))| \\
                        & = & |Line ~ Either String (Result Iden , Result (Sym "," :*> LineParser))| \\
                        & = & |Line ~ Either String (String , Result LineParser)| \\
                        & = & |Line ~ Either String (String , Line)|
  \end{eqnarray*}
  
  And the result is precisely the |HasIso| instance that we have for the type |Line|.
  In fact, we provide Template Haskell code to generate these mechanical isomorphisms
  automatically, the user would just call |$(deriveIso ''Line)|.
  
  
\subsection{Lexing Remarks}
\label{subsec:lexer}
    
  In the example we gave in figure \ref{fig:csv-parser} we use a few atomic grammar
  combinators that were left unexplained, such as |Iden| and |Sym ","|. The reason for this
  is that the semantics of these combinators depends on the underlying lexer being used.
  
  We provide a class |HasLexer lang| which ties this knot. It is fairly straight forward
  to use. The full, correct code, of the CSV example is shown below (where |a :<!> b| means
  parse |a| but only if it is \emph{not} followed by |b|).
  
\vskip 1em
\begin{code}
data CSV

instance HasLexer CSV where
  identStart _  ','   = False
  identStart _  '\n'  = False
  identStart _  _     = True  
  identLetter p       = identStart p
  reservedList _      = []
  
type CSVParser = VMany LineParser

type LineParser' 
  = Line  :<$>  Ident CSV :<!> Sym CSV ","
          :<|>  Ident CSV :<*> Sym CSV "," :*> LineParser
newtype LineParser = LP LineParser'

data Line = One String | More String Line
  deriving (Eq, Show, Ord)

$(deriveRec  ''LineParser ''LineParser')
$(deriveIso  ''Line)
\end{code} % $
\vskip .5em

  The |HasLexer lang| class defines lexing primitives for a language, which is specified through
  an empty data constructor. The type signature for |identStart|, for instance, is:

\vskip .5em
\begin{code}
  identStart :: Proxy lang -> Char -> Bool
\end{code} % $
\vskip .5em

  And it decides which characters start an identifier. For the readers familiar with
  \texttt{Text.Parsec}, our HasLexer is just a lifting from Parsec's lexing primitives
  to a typeclass.
  
\subsection{Pretty Printing}

  \begin{TODO}
    \item show the HasPrinter class.
    \item Mention the comments problem, and say that this is left as future work.
    \item Explain that |deriveRec| also devires a HasPrinter instance for the 
          encapsulated recursive type.
  \end{TODO}
  
\subsection{Summary}

  On this section we presented our \emph{grammar combinators} library with
  a simple use case. The important points the reader whould take are:
  
  \begin{itemize}
    \item Having type-level combinators to specify a language's grammar
          gives us an easy way to generate both a parser and a pretty-printer.
    \item Handling user defined types or mutually recursive grammars is not a problem.
    \item The type of the elements of a grammar is very regular, in fact, it is built
          using products, coproducts, units and lists (minus isomorphism for user defined types).
  \end{itemize}

  \warnme{Find a name for our library! : How about "Grammar Combinators"?}
  
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
  
  \bibliographystyle{plain}
  \bibliography{text/references}

\end{document}
