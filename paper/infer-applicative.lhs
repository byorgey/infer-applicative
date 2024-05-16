% -*- mode: LaTeX; compile-command: "./build.sh" -*-
\documentclass[sigplan,screen]{acmart}

%%
%% \BibTeX command to typeset BibTeX logo in the docs
\AtBeginDocument{%
  \providecommand\BibTeX{{%
    Bib\TeX}}}

%% Rights management information.  This information is sent to you
%% when you complete the rights form.  These commands have SAMPLE
%% values in them; it is your responsibility as an author to replace
%% the commands and values with those provided to you when you
%% complete the rights form.
\setcopyright{acmlicensed}
\copyrightyear{2024}
\acmYear{2024}
\acmDOI{XXXXXXX.XXXXXXX}

%% These commands are for a PROCEEDINGS abstract or paper.
\acmConference[ICFP '25]{The International Conference on Functional
  Programming}{September 10--12, 2025}{City, Country}
%%
%%  Uncomment \acmBooktitle if the title of the proceedings is different
%%  from ``Proceedings of ...''!
%%
%%\acmBooktitle{Woodstock '18: ACM Symposium on Neural Gaze Detection,
%%  June 03--05, 2018, Woodstock, NY}
\acmISBN{978-1-4503-XXXX-X/18/06}


%%
%% Submission ID.
%% Use this when submitting an article to a sponsored event. You'll
%% receive a unique submission ID from the organizers
%% of the event, and this ID should be used as the parameter to this command.
%%\acmSubmissionID{123-A56-BU3}

%%
%% The majority of ACM publications use numbered citations and
%% references.  The command \citestyle{authoryear} switches to the
%% "author year" style.
%%

\citestyle{acmauthoryear}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\let\Bbbk\undefined
%include polycode.fmt

%format A = "\square"
%format <$> = "\mathbin{\langle \$ \rangle}"
%format <*> = "\mathbin{\langle * \rangle}"
%format S = "\sigma"
%format T = "\tau"

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{amsmath,amssymb}
\usepackage{supertabular}
\usepackage{ifthen}

\input{ott/applicative_defns.tex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\term}[1]{\emph{#1}}

\begin{document}

%%
%% The "title" command has an optional parameter,
%% allowing the author to define a "short title" to be used in page headers.
\title{Idiomatic Inference}

\author{Brent A. Yorgey}
\email{yorgey@@hendrix.edu}
\orcid{0009-0005-0135-6134}
\affiliation{%
  \institution{Hendrix College}
  \city{Conway}
  \state{Arkansas}
  \country{USA}
}

\begin{abstract}
  McBride and Paterson's \emph{idioms}, or \emph{applicative
    functors}, are a well-known abstraction defining function
  application in some ambient effectful context.  It would be useful,
  especially in the context of designing domain-specific languages, to
  \emph{infer} such ``idiomatic'' application, allowing the programmer
  to use plain function application syntax.  We show that this is
  possible in a strong sense, by presenting a formally-verified type
  inference algorithm that can automatically infer uses of an
  applicative functor and insert appropriate coercions.  We also prove
  that this cannot lead to any ambiguity: in cases where there are
  multiple valid type-correct ways to insert coercions, the
  applicative functor laws guarantee that there is no observable
  difference.  We also extend our results to selective functors, but
  demonstrate via examples that inference for monads is inherently
  ambiguous.
\end{abstract}

%%
%% The code below is generated by the tool at http://dl.acm.org/ccs.cfm.
%% Please copy and paste the code instead of the example below.
%%
\begin{CCSXML}
<ccs2012>
 <concept>
  <concept_id>00000000.0000000.0000000</concept_id>
  <concept_desc>Do Not Use This Code, Generate the Correct Terms for Your Paper</concept_desc>
  <concept_significance>500</concept_significance>
 </concept>
 <concept>
  <concept_id>00000000.00000000.00000000</concept_id>
  <concept_desc>Do Not Use This Code, Generate the Correct Terms for Your Paper</concept_desc>
  <concept_significance>300</concept_significance>
 </concept>
 <concept>
  <concept_id>00000000.00000000.00000000</concept_id>
  <concept_desc>Do Not Use This Code, Generate the Correct Terms for Your Paper</concept_desc>
  <concept_significance>100</concept_significance>
 </concept>
 <concept>
  <concept_id>00000000.00000000.00000000</concept_id>
  <concept_desc>Do Not Use This Code, Generate the Correct Terms for Your Paper</concept_desc>
  <concept_significance>100</concept_significance>
 </concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Do Not Use This Code~Generate the Correct Terms for Your Paper}
\ccsdesc[300]{Do Not Use This Code~Generate the Correct Terms for Your Paper}
\ccsdesc{Do Not Use This Code~Generate the Correct Terms for Your Paper}
\ccsdesc[100]{Do Not Use This Code~Generate the Correct Terms for Your Paper}

%%
%% Keywords. The author(s) should pick words that accurately describe
%% the work being presented. Separate the keywords with commas.
\keywords{applicative, functor, inference, Agda}
%% A "teaser" image appears between the author and affiliation
%% information and the body of the document, and typically spans the
%% page.
% \begin{teaserfigure}
%   \includegraphics[width=\textwidth]{sampleteaser}
%   \caption{Seattle Mariners at Spring Training, 2010.}
%   \Description{Enjoying the baseball game from the third-base
%   seats. Ichiro Suzuki preparing to bat.}
%   \label{fig:teaser}
% \end{teaserfigure}

% \received{20 February 2007}
% \received[revised]{12 March 2009}
% \received[accepted]{5 June 2009}

\maketitle

\section{Introduction}

In most programming languages, if we have numeric variables |x| and |y|
and want to add them, we can do so using a simple expression like
\[ |x + y|. \] But what if one of the numbers might not exist?  For
example, perhaps the number was parsed from user input, which might
not be in the right format.  We can represent the possibly-failing
number using some kind of option type, such as |Maybe| in Haskell, XXX
in other languages.  But now the simple expression |x + y| no longer
typechecks, since |x| is (say) of type |Int|, whereas |y| has the
incompatible type (say) |Maybe Int|.  Of course, we can pattern-match
on $y$, taking an appropriate action in each case.  In Haskell, we
might write this as
\begin{code}
case y of
  Nothing  -> Nothing
  Just n   -> Just (x + n)
\end{code}
but now the fact that we are essentially performing an addition
operation has been obscured by a lot of syntax.  If both |x| and |y|
might be undefined, the situation is even worse.

In the Haskell community, \term{applicative functors}, first
introduced by McBride and Paterson XXX cite, are a well-known solution
to this problem.  An applicative functor is any type constructor |A|
which supports operations |pure| and |ap| having the following
polymorphic types (together with some appropriate laws):
\begin{gather*}
|pure : t -> A t| \\
|ap : A (s -> t) -> (A s -> A t)|
\end{gather*}
That is, |pure| gives us a way to inject plain values of any type |t|
into the type |A t|, and |ap| allows us to distribute |A| over arrows.

For convenience, define |(<*>) = ap|, and
\begin{code}
(<$>) :: (a -> b) -> (A a -> A b)
f <$> x = pure f <*> x
\end{code}
Since |Maybe| is an applicative functor (with |pure = Just| and |ap|
left as an exercise for the reader), if |x, y :: Maybe Int| we can
add them like so:
\[
|(+) <$> x <*> y :: Maybe Int|.
\]

This is certainly much better than writing out nested |case|
statements; it is relatively short and makes it more obvious that we
are doing an addition operation, modulo some details about handling
potential failure.

But it's not good enough!  The |<$>| and |<*>| still introduce
syntactic noise.  XXX Haskell experts are OK with this but 

XXX not arguing Haskell should be extended; good reasons Haskell can't
handle this.  DSLs are where the idea really shines\dots

\section{Applicative inference for DSLs}

Examples of DSLs that really benefit from applicative inference.

\begin{itemize}
\item Swarm world DSL
\item \dots
\end{itemize}

\section{Applicative inference by example}

XXX Some examples showing how to do inference

XXX Examples showing that it doesn't matter how we insert coercions

XXX Examples showing that we can't infer monads.

\section{Subtyping for applicative inference}

We begin with a simple type system, shown in XXX Fig. \ref{fig:types}.
\begin{figure}[htp]
  \centering
  \ottgrammartabular{\otttype\ottafterlastrule}
  \caption{Types}
  \label{fig:types}
\end{figure}

Now we define a subtyping relation over these types, shown in XXX
Fig. \ref{fig:subtyping}.  The first four rules are fairly standard:
the subtyping relation is reflexive and transitive, has the usual
contravariant/covariant rule for function arrows, and is a congruence
with respect to |A|.  The last two rules are more interesting, and
simply reflect the fact that we want to be able to implicitly insert
|pure| and |ap| as needed.  Thus, we consider any type |T| a subtype
of |A T| (corresponding to an implicit call to |pure|), and
similarly we consider |A (S -> T)| a subtype of |(A S -> A
T)| (corresponding to |ap|).

\begin{figure}[htp]
  \centering
  \ottdefnsub{}
  \caption{Subtyping}
  \label{fig:subtyping}
\end{figure}

XXX now introduce terms with standard type system.

% The ``\verb|figure|'' environment should be used for figures. One or
% more images can be placed within a figure. If your figure contains
% third-party material, you must clearly identify it as such, as shown
% in the example below.
% \begin{figure}[h]
%   \centering
%   \includegraphics[width=\linewidth]{sample-franklin}
%   \caption{1907 Franklin Model D roadster. Photograph by Harris \&
%     Ewing, Inc. [Public domain], via Wikimedia
%     Commons. (\url{https://goo.gl/VLCRBB}).}
%   \Description{A woman and a girl in white dresses sit in an open car.}
% \end{figure}



\begin{acks}
Acknowledgements.
\end{acks}

%%
%% The next two lines define the bibliography style to be used, and
%% the bibliography file.
\bibliographystyle{ACM-Reference-Format}
\bibliography{references}

\appendix

\section{Proofs}

\end{document}
\endinput
%%
%% End of file `sample-sigplan.tex'.