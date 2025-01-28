%% -*- mode: LaTeX; compile-command: "./Shake.hs" -*-

\documentclass[xcolor=svgnames,12pt,aspectratio=169]{beamer}

%include polycode.fmt

%format BOX = "\square"
%format cases = "\mathbf{cases}"
%format <$> = "\mathbin{\langle \$ \rangle}"
%format <*> = "\mathbin{\langle * \rangle}"

\usepackage{xspace}
\usepackage{ulem}
\usepackage{qtree}
\usepackage{graphicx}
\graphicspath{{images/}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
        \includegraphics[width=3in]{\sectionimg}
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
\author{Brent Yorgey}
% \titlegraphic{\includegraphics[width=1in]{tree}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\begin{xframe}{}
  \titlepage
\end{xframe}

XXX pick section images
\def\sectionimg{egypt}
\section{Introduction}

\begin{xframe}{Swarm}
  XXX include Swarm screenshot
  \note{So I have this game \dots}
\end{xframe}

\begin{xframe}{World generation DSL}
  XXX show example world DSL code + resulting world (maybe even a
  couple different examples, one slide each)
\end{xframe}

\begin{xframe}{Types?}
  XXX get rid of bullets, reveal one at a time
  \begin{itemize}
  \item In general, |W a = Coords -> a|.
  \item A top-level expression describing a world has type |W Cell|.
  \item |x, y : W Int|.
  \item |if (x > 3) grass water : W Cell| ?
  \end{itemize}
\end{xframe}

\begin{xframe}{Another example}
  |if uniform(0,1) > 0.2 then "hello" else "world" : Distribution String|
\end{xframe}

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
    |type W a = Coords -> a| \\
    |pure : a -> W a = const| \\
    |ap : W (a -> b) -> W a -> W b = \f x c -> f c (x c)|
  \end{center}
\end{xframe}

\begin{xframe}{Example: |W|}
  \begin{center}
    |if (x > 3) grass water : W Cell| \bigskip

    $\Downarrow$ \bigskip

    |ap (ap (pure if) (ap (ap (pure (>)) x) (pure 3)) (pure grass)) (pure water)| \bigskip

    $=$ \bigskip

    |if <$> ((>) <$> x <*> pure 3) <*> pure grass <*> pure water|
  \end{center}
\end{xframe}

\begin{xframe}{Question}
  \begin{center}
    How and when can we automatically insert |pure| and |ap|?
  \end{center}
\end{xframe}

\section{Formalization}

\section{Applicative Subtyping}
\section{Ambiguity and Coherence}

\end{document}
