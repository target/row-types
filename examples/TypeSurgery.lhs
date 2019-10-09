\documentclass[11pt, letterpaper]{article}

\usepackage[margin=1in]{geometry}
\usepackage{hyperref}

%include polycode.fmt
%format ≈ = "\ensuremath{\approx}"
%format *> = "\mathop{*\!\!\!>}"
%format # = "~\texttt{\#}"
%format @ = "~@"

%format .+ = "\mathbin{\color{BlueViolet}{.\!+}}"
%format .! = "\mathbin{\color{BlueViolet}{.!}}"
%format .- = "\mathbin{\color{BlueViolet}{.\!-}}"
%format .== = "\mathbin{\color{BlueViolet}{.\!\!=\joinrel=}}"

\usepackage[dvipsnames]{xcolor}
\newcommand{\id}[1]{\textsf{\textsl{#1}}}
\renewcommand{\Varid}[1]{\textcolor{Sepia}{\id{#1}}}
\renewcommand{\Conid}[1]{\textcolor{OliveGreen}{\id{#1}}}
%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"

\title{Type Surgery}
\author{Daniel Winograd-Cort}
\date{April 2019}

\begin{document}

\maketitle

\section{Type Surgery}

I read about the idea of ``data type surgery'' on
\href{https://blog.poisson.chat/posts/2018-11-26-type-surgery.html}
{Lysxia's blog post of the same name}.  I'll quote from the blog:

\begin{quote}
The general motivation is to improve the applicability of various generic definitions,
such as aeson’s generic instances for |ToJSON| and |FromJSON|. Such a library often
offers several options to customize the generic implementations, but it can still
happen that none of them quite fit your external requirements and you have to resort
to manual implementations, even with only small mismatches with the generic
implementations. Surgeries are a new way to adapt generic implementations to such
conditions outside of your control.
\end{quote}

As it turns out, one can gain the same powers from the row-types package
(something Lysxia hinted at in a footnote in the original blog).  Today, I'm going
to demonstrate how to use row-types to do type surgery.

\iffalse
\begin{code}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PartialTypeSignatures #-}
module TypeSurgery where

import Data.Row
import qualified Data.Row.Records as Rec

import Data.Aeson
import Data.Aeson.Types       (Parser)
import Data.Coerce            (coerce)
import Data.Functor.Identity  (Identity(..))

import GHC.Generics

-- Convenient lens functions (rather than importing Lens)
over :: ((a -> Identity b) -> s -> Identity t) -> (a -> b) -> s -> t
over = coerce

\end{code}
\fi

\subsection{Example}

I'll use the same example given in Lysxia's blog:

\begin{code}
data RecToy = RecToy
  { iden     :: Int
  , header1  :: Int
  , header2  :: Int
  , payload  :: String
  } deriving (Eq, Show, Generic, ToJSON)
\end{code}


Here we have a toy record for which we'd like to generate a |FromJSON| instance,
but we have a condition: the |payload| field is allowed to be optional in the
JSON (i.e., a missing field should be parsed as the empty string |""|).  Aeson's
generic instances work fine with optional fields \emph{so long as they are |Maybe|
fields}, so there seems to be no easy solution.  We could make an alternate
|RecToy'| whose |payload| field is a |Maybe String| and then convert it, but that's
a lot of boilerplate.  We could also write our own |FromJSON| instance manually,
but that's tedious.

So, let's do some surgery!

\subsection{generic-data-surgery}
Lyxsia describes the following solution using the generic-data-surgery library:

\begin{spec}
instance FromJSON RecToy where
  parseJSON :: Value -> Parser RecToy
  parseJSON
    = fmap  ( fromOR
            . modifyRField @"payload" defString
            . toOR')
    . genericParseJSON defaultOptions{omitNothingFields=True}

defString :: Maybe String -> String
defString = maybe "" id
\end{spec}

The key part here is the surgery going on in:
\begin{spec}
fromOR . modifyRField @"payload" defString . toOR'
\end{spec}
Let's break this down:
\begin{itemize}
\item First, we head into the ``operating room'' with |toOR'|.
\item Then, we modify the record field named |payload| by applying the |defString|
  function to it.
\item Finally, we exit the ``operating room'' with |fromOR|.
\end{itemize}

Behind the scenes at the type level, the |genericParseJSON| is being done on a
synthetic type that looks just like |RecToy| but where the |payload| field has
the type |Maybe String|.  This synthetic type is lifted into the ``operating room'',
which is essentially lifting it into a manipulatable type and then ``operated on'',
where the |payload| field is converted from type |Maybe String| to |String| using
the |defString| function.  Finally, |fromOR| converts this manipulatable type
to |RecToy|, and parsing is complete.

\subsection{row-types Solution}
For a simple case like this, we can do almost the same thing with row-types.
The main difference is that what generic-data-surgery calls an operating room,
we simply call a row-types record (or variant).  Indeed, instead of going to and
from the OR, we go to and from the native type using |Rec.toNative| and
|Rec.fromNative|.  Specifically:
\begin{itemize}
\item In place of |toOR'|, we call |Rec.fromNative| to convert from a native Haskell
  type to a row-types record.
\item In place of |modifyRField @"payload" defString|, we do a lensy operation
  to change the record.  In this case, we could write
  |over (Rec.focus #payload) defString|.
\item Finally, we convert back to a Haskell native type with |Rec.toNativeExact|.
  Note that |toNativeExact| is a restricted version of |toNative| that forces the
  native type and the record to have the exact same fields while |toNative| allows
  the record to have extraneous fields.  As such, |toNativeExact| often improves
  type inference.
\end{itemize}
The full code looks like:
\begin{code}
instance FromJSON RecToy where
  parseJSON :: Value -> Parser RecToy
  parseJSON
    = fmap  ( Rec.toNativeExact
            . over (Rec.focus #payload) defString)
    . genericParseJSON defaultOptions{omitNothingFields=True}

defString :: Maybe String -> String
defString = maybe "" id
\end{code}

\subsection{Limitations}
The row-types library is limited compared to generic-data-surgery in two specific
ways: there are no conversion functions between full sum-of-products Haskell
data types and variants of records, and there is no support for unnamed fields.
The first limitation is simply because such a feature has never seemed necessary
to row-types, and it could be added with a little generics programming.

The second is a more fundamental limitation.  Names are critical to the concept
of the row-types library, as every field in a record and every possibility in a
variant must be named.  Therefore, it is simply impossible to convert a native
record that has no field names into a row-types record (without a lot of defaulting).

\end{document}
