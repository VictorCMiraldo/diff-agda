\documentclass{llncs}
\usepackage[english]{babel}
\usepackage{savesym}
\usepackage{amsmath}
\usepackage{wrapfig}
\usepackage{hyperref}
\usepackage{catchfilebetweentags}
\usepackage{agda}
\usepackage[all]{xypic}

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
  no conflicting edits. Implementing a tool that knows the semantics of any file we happen 
  to need, however, is no simple task, specially given the plethora of file formats we see nowadays. 
  
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
  \vline
  \begin{minipage}[t]{.3\textwidth}
    \begin{verbatim}
items      ,qty ,unit
cake-flour ,1   ,cp
eggs       ,2   ,units
sugar      ,1   ,tsp
  \end{verbatim}
  \begin{center}Bob\end{center}
  \end{minipage}
  \end{center}
  \caption{CSV files}
  \label{fig:csvfiles}
  \end{figure}
  
  It is not hard to see that Alice's and Bob's edits, in figure \ref{fig:csvfiles} do \emph{not} conflict. However,
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
  same time, acts as the \emph{type} of a language. We want to have type constructors
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
  that any Haskell type is isomorphic, by definition, to a sum-of-products, which can be expressed
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
  instance (which is nothing more than the initial algebra for the underlying functor):
  
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
  
  Even though we still have something of type |Line| on the right-hand-side of our isomorphism,
  that does not represent a problem as the instances will open it into another sum-of-products
  whenever needed. This is possible since the instance chosing is guided by induction
  in our grammar combinators, and a |LineParser| is always \emph{tagged} by |Line|.
  
  
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
  \texttt{Text.Parsec}, our |HasLexer| is just a lifting from Parsec's lexing primitives
  to a typeclass. In fact, we use \texttt{Text.Parsec} and \texttt{Text.PrettyPrint} as our
  underlying libraries for parsing and printing.
  
\subsection{Pretty Printing}

  Generating a pretty-printer is analogous to generating a parser, with the difference
  that a few combinators will have the same parsing behaviour but not the same
  pretty printing behaviour.
  
  Our |HasPrinter| class also needs to access the |Result| type family declared
  in the |HasParser| class. We therefore assume that |HasParser a => HasPrinter a|.
  
\vskip .5em
\begin{code}
  class (HasParser a) => HasPrinter a where
    pp :: Proxy a -> Result a -> Doc
\end{code}
\vskip .5em

  The |deriveRec| template haskell directive will also generate a |HasPrinter| instance
  for an encapsulated type.
  
  If we require our pretty printer and parser to be an isomorphism, we run into a few problems.
  Namelly, this isomorphism has to be modulo formating and comments. These problems are
  left as future work.
  
\subsection{Summary}

  On this section we presented our \emph{grammar combinators} library with
  a simple use case. We showed how to encode a language's grammar on Haskell
  type-level, which allows us to generate both a parser and a pretty printer for it.
  We proposed a solution for handling mutually recursive and user defined types.
  
  The advantages of this approach are many. On one side, it is easy to do generic
  programming on the elements resulting from our parsers, once the target types
  are all built using products, coproducts, unit and lists (minus isomorphism for user defined types).
  On the other hand, it is extensible! For a user can always define new domain-specific
  combinators and immediatly integrate them with the rest of the library.
  
  In the following sections we give the intuition behind what captures differences
  in a type |a|. As expected, this definition follows by induction on the structure of |a|.
  Later, we show how we proved that this definition of a \emph{diff} is correct, in Agda.
  
  
  
\section{Structure-aware Diffing}
  
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
