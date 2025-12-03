%% -*- mode: LaTeX; compile-command: "./Shake.hs" -*-

\documentclass[xcolor=svgnames,12pt,aspectratio=169]{beamer}

%include polycode.fmt

%format BOX = "\square"
%format cases = "\mathbf{cases}"
%format <$> = "\mathbin{\langle \$ \rangle}"
%format <*> = "\mathbin{\langle * \rangle}"

\usepackage{amsmath}
\usepackage{wasysym}
\usepackage{xspace}
\usepackage{ulem}
\usepackage{qtree}
\usepackage{graphicx}
\graphicspath{{images/}}
\usepackage{supertabular}
\usepackage{ifthen}
\usepackage{pgf}

\input{../../ott/applicative_defns.tex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newtheorem{thm}{Theorem}
\newtheorem{conj}{Conjecture}
\newtheorem{fls}{Not A Theorem \frownie}

\newcommand{\etc}{\textit{etc.}}
\newcommand{\eg}{\textit{e.g.}\xspace}
\newcommand{\ie}{\textit{i.e.}\xspace}

\newcommand{\thevenue}{Portland State PLV Seminar}
\newcommand{\thedate}{30 January 2025}

\newcounter{langcounter}
\newcommand{\lang}[1]{\stepcounter{langcounter}{\Large \arabic{langcounter}. #1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\setbeamertemplate{items}[circle]

\mode<presentation>
{
  \usetheme{default}                          % use a default (plain) theme

  \setbeamertemplate{navigation symbols}{}    % don't show navigation
                                              % buttons along the
                                              % bottom
  \setbeamerfont{normal text}{family=\sffamily}

  % XX remove this before giving actual talk!
  % \setbeamertemplate{footline}[frame number]
  % {%
  %   \begin{beamercolorbox}{section in head/foot}
  %     \vskip2pt
  %     \hfill \insertframenumber
  %     \vskip2pt
  %   \end{beamercolorbox}
  % }

  \AtBeginSection[]
  {
    \begin{frame}<beamer>
      \frametitle{}

      \begin{center}
        \includegraphics[width=3in,height=2in,keepaspectratio=true]{\sectionimg}
        \bigskip

        {\Huge \usebeamercolor[fg]{title}\insertsectionhead}
      \end{center}
    \end{frame}
  }
}

\newcommand{\sectionimg}{}

\defbeamertemplate*{title page}{customized}[1][]
{
  \vbox{}
  \vfill
  \begin{centering}
    \begin{beamercolorbox}[sep=8pt,center,#1]{title}
      \usebeamerfont{title}\inserttitle\par%
      \ifx\insertsubtitle\@@empty%
      \else%
        \vskip0.25em%
        {\usebeamerfont{subtitle}\usebeamercolor[fg]{subtitle}\insertsubtitle\par}%
      \fi%
    \end{beamercolorbox}%
    \vskip1em\par
    {\usebeamercolor[fg]{titlegraphic}\inserttitlegraphic\par}
    \vskip1em\par
    \begin{beamercolorbox}[sep=8pt,center,#1]{author}
      \usebeamerfont{author}\insertauthor
    \end{beamercolorbox}
    \begin{beamercolorbox}[sep=8pt,center,#1]{institute}
      \usebeamerfont{institute}\insertinstitute
    \end{beamercolorbox}
    \begin{beamercolorbox}[sep=8pt,center,#1]{date}
      \usebeamerfont{date}\insertdate
    \end{beamercolorbox}
  \end{centering}
  \vfill
}

\newenvironment{xframe}[1][]
  {\begin{frame}[fragile,environment=xframe,#1]}
  {\end{frame}}

% uncomment me to get 4 slides per page for printing
% \usepackage{pgfpages}
% \pgfpagesuselayout{4 on 1}[uspaper, border shrink=5mm]

% \setbeameroption{show notes}

\renewcommand{\emph}{\textbf}

\title{Idiomatic Inference for DSLs}
\date{\thevenue \\ \thedate}
\author{Brent Yorgey \\ Hendrix College}
% \titlegraphic{\includegraphics[width=1in]{tree}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\begin{xframe}{}
  \titlepage
\end{xframe}

\def\sectionimg{swarm-world}
\section{Motivation}

\begin{xframe}{Swarm}
  \begin{center}
    \includegraphics[width=3in]{main-menu} \bigskip

    \url{https://swarm-game.github.io/}
  \end{center}
  \note{So I have this game \dots}
\end{xframe}

\begin{xframe}{World generation DSL}
  \begin{center}
    \begin{minipage}{0.4\textwidth}
      \begin{center}
        \tiny
\begin{verbatim}
let
  pn0 = perlin seed 6 0.05 0.6,
  pn1 = perlin (seed + 1) 6 0.05 0.6,
  ...
in
overlay
[ mask (big && hard && artificial)
    (if (cl > 0.85) then {stone, copper ore} else {stone})
, mask (big && hard && natural)
  ( overlay
    [ {grass}
    , mask (cl > 0.0)
        (if (hash % 30 == 1)
          then {dirt, LaTeX}
          else {dirt, tree})
    , mask (hash % 30 == 0) {stone, boulder}
    , mask (cl > 0.5) {stone, mountain}
    ]
  )
, ...
]
\end{verbatim}
      \end{center}
    \end{minipage}
    \begin{minipage}{0.5\textwidth}
      \begin{center}
        \includegraphics[width=\textwidth]{swarm-world}
      \end{center}
    \end{minipage}
  \end{center}
\end{xframe}

\begin{xframe}{World generation DSL}
  \begin{center}
    \begin{minipage}{0.5\textwidth}
      \begin{center}
        |grass|
      \end{center}
    \end{minipage}
    \hspace{0.3in}
    \begin{minipage}{0.4\textwidth}
      \begin{center}
        \includegraphics[width=\textwidth]{grass}
      \end{center}
    \end{minipage}
  \end{center}
\end{xframe}

\begin{xframe}{World generation DSL}
  \begin{center}
    \begin{minipage}{0.4\textwidth}
      \begin{center}
        |if (x > 3) then water else grass|
      \end{center}
    \end{minipage}
    \hspace{0.3in}
    \begin{minipage}{0.4\textwidth}
      \begin{center}
        \includegraphics[width=\textwidth]{grass-water}
      \end{center}
    \end{minipage}
  \end{center}
\end{xframe}


\begin{xframe}{Types?}
  \begin{itemize}
  \item<+-> |W a = (Int, Int) -> a|.
  \item<+-> A top-level expression describing a world has type |W Cell|.
  \item<+-> |grass, water : Cell|
  \item<+-> |if : Bool -> a -> a -> a|
  \item<+-> |x, y : W Int|
  \item<+-> |if (x > 3) then water else grass : W Cell| ?
  \end{itemize}
\end{xframe}

\begin{xframe}{Another example}
  |if uniform(0,1) > 0.2 then "hello" else "world" : Distribution String|
\end{xframe}

\def\sectionimg{IdiomLite}
\section{Applicative Functors}

\begin{xframe}{Definition}
  An \emph{applicative functor} is some |BOX : Type -> Type| together
  with operations
  \begin{center}
  |pure : a -> BOX a| \\
  |ap : BOX (a -> b) -> BOX a -> BOX b|
  \end{center}
  (satisfying certain laws).
\end{xframe}

\begin{xframe}{Convenience}
  For convenience, define
  \begin{itemize}
  \item |(<*>) = ap|
  \item |(<$>) = fmap = ap . pure : (a -> b) -> BOX a -> BOX b|
  \end{itemize}
  So \emph{e.g.} |ap (ap (pure (>)) x) (pure 3)| can be written \[
    |(>) <$> x <*> pure 3| \]
\end{xframe}

\begin{xframe}{Example: |Maybe|}
  \begin{center}
    |pure = Just| \\
    |ap = \cases {(Just f) (Just x) -> Just (f x); _ _ -> Nothing}|
  \end{center}
\end{xframe}

\begin{xframe}{Example: |W|}
  \begin{center}
    |type W a = (Int, Int) -> a| \\
    |pure : a -> W a = const| \\
    |ap : W (a -> b) -> W a -> W b = \f x c -> f c (x c)|
  \end{center}
\end{xframe}

\begin{xframe}{Example: |W|}
  \begin{center}
    |if (x > 3) then water else grass : W Cell| \bigskip

    $\Downarrow$ \bigskip

    |ap (ap (pure if) (ap (ap (pure (>)) x) (pure 3)) (pure water)) (pure grass)| \bigskip

    $=$ \bigskip

    |if <$> ((>) <$> x <*> pure 3) <*> pure water <*> pure grass|
  \end{center}
\end{xframe}

\begin{xframe}{Question}
  \begin{center}
    How and when can we automatically insert |pure| and |ap|? \bigskip

    \onslide<2>{Implemented in Swarm world DSL\dots but is it correct?  And
      how does it generalize?}
  \end{center}
\end{xframe}

\def\sectionimg{principia}
\section{Formalization}

\begin{xframe}{}
  \ottgrammartabular{\ottterm\ottinterrule\otttype\ottafterlastrule}
\end{xframe}

\begin{xframe}{}
\begin{ottdefnblock}[#1]{$\Gamma  \vdash  \ottnt{t}  \ottsym{:}  \tau$}{\ottcom{$\ottnt{t}$ has type $\tau$ in context $\Gamma$}}
\ottusedrule{\ottdruletyXXvar{}}
\ottusedrule{\ottdruletyXXlam{}}
\ottusedrule{\ottdruletyXXapp{}}
\ottusedrule{\ottdruletyXXconst{}}
\end{ottdefnblock}
\end{xframe}

\begin{xframe}{}
\begin{ottdefnblock}{$\Gamma  \vdash  \ottnt{t}  \ottsym{:}  \tau$}{\ottcom{$\ottnt{t}$ has type $\tau$ in context $\Gamma$}}
\ottusedrule{\ottdruletyXXpure{}}
\ottusedrule{\ottdruletyXXap{}}
\end{ottdefnblock}
\end{xframe}

\begin{xframe}{}
  \begin{center}
    So far, |pure| and |ap| must be explicitly included\dots how to
    model the possibility to infer them? \bigskip

    \onslide<2>{Subtyping!}
  \end{center}
\end{xframe}

\begin{xframe}{}
\begin{ottdefnblock}{$\tau_{{\mathrm{1}}}  \mathrel{<:}  \tau_{{\mathrm{2}}}$}{\ottcom{$\tau_{{\mathrm{1}}}$ is a subtype of $\tau_{{\mathrm{2}}}$}}
\ottusedrule{\ottdrulesubXXrefl{}}
\ottusedrule{\ottdrulesubXXtrans{}}
\ottusedrule{\ottdrulesubXXarr{}}
\end{ottdefnblock}
\end{xframe}

\begin{xframe}{}
\begin{ottdefnblock}{$\tau_{{\mathrm{1}}}  \mathrel{<:}  \tau_{{\mathrm{2}}}$}{\ottcom{$\tau_{{\mathrm{1}}}$ is a subtype of $\tau_{{\mathrm{2}}}$}}
\ottusedrule{\ottdrulesubXXpure{}}
\ottusedrule{\ottdrulesubXXap{}}
\end{ottdefnblock}
\end{xframe}

\begin{xframe}{}
\begin{ottdefnblock}{$\tau_{{\mathrm{1}}}  \mathrel{<:}  \tau_{{\mathrm{2}}}$}{\ottcom{$\tau_{{\mathrm{1}}}$ is a subtype of $\tau_{{\mathrm{2}}}$}}
\ottusedrule{\ottdrulesubXXbox{}}
\end{ottdefnblock}
\end{xframe}

\begin{xframe}{}
  \ottdefnstype{}
\end{xframe}

\begin{xframe}{Elaboration}
  \begin{itemize}
  \item $\sigma \mathrel{<:} \tau$ elaborates to an explicit coercion term with type
    $\sigma \to \tau$
  \item $\Gamma \vdash_{<:} t : \tau$ elaborates to $\Gamma \vdash t'
    : \tau$, where all uses of subtyping have been replaced by an
    application of an elaborated coercion term
  \end{itemize}
\end{xframe}

\begin{xframe}{}
  \begin{center}
    Question: is $\sigma <: \tau$ decidable?
  \end{center}
\end{xframe}

\def\sectionimg{sub}
\section{Applicative Subtyping}

\begin{xframe}{Transitivity is annoying}
\ottusedrule{\ottdrulesubXXtrans{}}
\end{xframe}

\begin{xframe}{Transitivity-free subtyping}
\begin{ottdefnblock}[#1]{$\tau_{{\mathrm{1}}}  \vartriangleleft  \tau_{{\mathrm{2}}}$}{\ottcom{$\tau_{{\mathrm{1}}}$ is a subtype of $\tau_{{\mathrm{2}}}$}}
\ottusedrule{\ottdrulesubtXXrefl{}}
\ottusedrule{\ottdrulesubtXXarr{}}
\end{ottdefnblock}
\end{xframe}

\begin{xframe}{Transitivity-free subtyping}
\begin{ottdefnblock}[#1]{$\tau_{{\mathrm{1}}}  \vartriangleleft  \tau_{{\mathrm{2}}}$}{\ottcom{$\tau_{{\mathrm{1}}}$ is a subtype of $\tau_{{\mathrm{2}}}$}}
\ottusedrule{\ottdrulesubtXXbox{}}
\ottusedrule{\ottdrulesubtXXpure{}}
\ottusedrule{\ottdrulesubtXXap{}}
\onslide<2>{\ottusedrule{\ottdrulesubtXXpureap{}}}
\end{ottdefnblock}
\end{xframe}

\begin{xframe}{Transitivity-free subtyping}
\begin{center}
  $(\sigma <: \tau) \iff (\sigma \vartriangleleft \tau)$: Proved in Agda! $\checkmark$
\end{center}
\end{xframe}

\begin{xframe}{Tree model}
  \begin{center}
    |B -> B| \bigskip

    \input{diagrams/B->B.pgf}
  \end{center}
\end{xframe}

\begin{xframe}{Tree model}
  \begin{center}
    |(B -> B) -> B| \bigskip

    \input{diagrams/(B->B)->B.pgf}
  \end{center}
\end{xframe}

\begin{xframe}{Tree model}
  \begin{center}
    |B -> BOX B| \bigskip

    \input{diagrams/B->xB.pgf}
  \end{center}
\end{xframe}

\begin{xframe}{Tree model}
  \begin{center}
    |BOX (B -> B)| \bigskip

    \input{diagrams/x(B->B).pgf}
  \end{center}
\end{xframe}

\begin{xframe}{Subtyping rules}
  \begin{center}
    \input{diagrams/box-rules.pgf}
  \end{center}
\end{xframe}

\begin{xframe}{Subtyping}
  \begin{center}
    \input{diagrams/chains.pgf}
  \end{center}
\end{xframe}

\begin{xframe}{So: is subtyping decidable?}
  \begin{center}
    \dots probably?  But\dots tricky! \bigskip

    \input{diagrams/random.pgf}
  \end{center}
\end{xframe}

\def\sectionimg{duck-rabbit}
\section{Ambiguity and Coherence}

\begin{xframe}{Coherence}
  \begin{thm}
    Any two derivations of $\Gamma \vdash_{<:} t : \tau$ elaborate
    to terms that are equivalent up to $\beta$, $\eta$, and the
    applicative laws.
  \end{thm}

  \note{Really important since it means there are no surprises for the
  programmer and no dependence on hidden behavior of inference algorithm.

  Unfortunately, this is false!!}
\end{xframe}

\begin{xframe}{\sout{Coherence}}
  \begin{fls}
    Any two derivations of $\Gamma \vdash_{<:} t : \tau$ elaborate
    to terms that are equivalent up to $\beta$, $\eta$, and the
    applicative laws.
  \end{fls}
\end{xframe}

\begin{xframe}{Counterexample}
  \begin{center}
    |\x -> x : BOX B -> BOX BOX B| \bigskip

  \begin{minipage}{0.4\linewidth}
    \begin{align*}
      &\phantom{<:} |B -> B| \\
      &<: |B -> BOX B| \\
      &<: |BOX(B -> BOX B)| \\
      &<: |BOX B -> BOX BOX B| \\
      &\rightsquigarrow |fmap pure|
    \end{align*}
  \end{minipage}
  \begin{minipage}{0.4\linewidth}
    \begin{align*}
      &\phantom{<:} |B -> B| \\
      &<: |BOX (B -> B)| \\
      &<: |BOX BOX (B -> B)| \\
      &<: |BOX (BOX B -> BOX B)| \\
      &<: |BOX BOX B -> BOX BOX B| \\
      &<: |BOX B -> BOX BOX B| \\
      &\rightsquigarrow |pure|
    \end{align*}
  \end{minipage}
  \end{center}
\end{xframe}

\begin{xframe}{No nesting?}
  \begin{center}
    Intuitively, the problem has to do with nested boxes, like |BOX
    BOX B|. \bigskip

    But we often don't need or want that.
  \end{center}
\end{xframe}

\begin{xframe}{}
  Call a type ``boxbox-free'' if it has no immediately nested boxes. \medskip
  \begin{conj}[Coherence]
    Any two derivations of $\Gamma \vdash_{<:} t : \tau$ elaborate to
    terms that are equivalent up to $\beta$, $\eta$, and the
    applicative laws, \emph{as long as all embedded subtyping
    judgments are boxbox-free}.
  \end{conj}
\end{xframe}

\begin{xframe}{}
  \begin{conj}
    If $\tau$ and all the types in $\Gamma$ are boxbox-free, then so
    are all the types that show up anywhere in a derivation $\Gamma
    \vdash_{<:} t : \tau$.
  \end{conj}

  \onslide<2->{In particular, if $\Gamma = \varnothing$ and the final type we
  want has a single box, then there can never be any nested boxes
  anywhere. \medskip}

  \onslide<3>{Definitely not true for monads! |join : BOX BOX a -> BOX
  a| lets us hide nested boxes anywhere.}
\end{xframe}

\def\sectionimg{future}
\section{Future Work}

\begin{xframe}{Future Work}
  \begin{itemize}
  \item Prove conjectures / find the right things to prove
  \item Explore how to write effective + efficient inference procedures
  \item Incorporate product and sum types
  \item Extend to selective functors
  \end{itemize}
\end{xframe}

\end{document}
