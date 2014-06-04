\name{rational-class}
\Rdversion{1.1}
\docType{class}
\alias{rational-class}
\alias{-,numeric,rational-method}
\alias{-,polynomial,rational-method}
\alias{-,rational,numeric-method}
\alias{-,rational,polynomial-method}
\alias{-,rational,rational-method}
\alias{/,numeric,rational-method}
\alias{/,polynomial,rational-method}
\alias{/,rational,numeric-method}
\alias{/,rational,polynomial-method}
\alias{/,rational,rational-method}
\alias{*,numeric,rational-method}
\alias{*,polynomial,rational-method}
\alias{*,rational,numeric-method}
\alias{*,rational,polynomial-method}
\alias{*,rational,rational-method}
\alias{+,numeric,rational-method}
\alias{+,polynomial,rational-method}
\alias{+,rational,numeric-method}
\alias{+,rational,polynomial-method}
\alias{+,rational,rational-method}
\alias{print,rational-method}

\title{Class \code{"rational"}}
\description{
Ratios of polynomials
}
\section{Objects from the Class}{
Objects can be created by calls of the form \code{rational(num, den)},
where \code{num} and \code{den} are acceptable to \code{as.polynomial}.
}
\section{Slots}{
  The numerator and denominator coefficients are stored un-factored.
  \describe{
    \item{\code{num}:}{Object of class \code{"polynomial"} ~~ }
    \item{\code{den}:}{Object of class \code{"polynomial"} ~~ }
  }
}
\section{Methods}{
  Arithmetic that implicitly converts numeric and polynomial classes up to
  rational are provided.
  \describe{
    \item{-}{\code{signature(e1 = "numeric", e2 = "rational")}: ... }
    \item{-}{\code{signature(e1 = "polynomial", e2 = "rational")}: ... }
    \item{-}{\code{signature(e1 = "rational", e2 = "numeric")}: ... }
    \item{-}{\code{signature(e1 = "rational", e2 = "polynomial")}: ... }
    \item{-}{\code{signature(e1 = "rational", e2 = "rational")}: ... }
    \item{/}{\code{signature(e1 = "numeric", e2 = "rational")}: ... }
    \item{/}{\code{signature(e1 = "polynomial", e2 = "rational")}: ... }
    \item{/}{\code{signature(e1 = "rational", e2 = "numeric")}: ... }
    \item{/}{\code{signature(e1 = "rational", e2 = "polynomial")}: ... }
    \item{/}{\code{signature(e1 = "rational", e2 = "rational")}: ... }
    \item{*}{\code{signature(e1 = "numeric", e2 = "rational")}: ... }
    \item{*}{\code{signature(e1 = "polynomial", e2 = "rational")}: ... }
    \item{*}{\code{signature(e1 = "rational", e2 = "numeric")}: ... }
    \item{*}{\code{signature(e1 = "rational", e2 = "polynomial")}: ... }
    \item{*}{\code{signature(e1 = "rational", e2 = "rational")}: ... }
    \item{+}{\code{signature(e1 = "numeric", e2 = "rational")}: ... }
    \item{+}{\code{signature(e1 = "polynomial", e2 = "rational")}: ... }
    \item{+}{\code{signature(e1 = "rational", e2 = "numeric")}: ... }
    \item{+}{\code{signature(e1 = "rational", e2 = "polynomial")}: ... }
    \item{+}{\code{signature(e1 = "rational", e2 = "rational")}: ... }
    \item{print}{\code{signature(x = "rational")}: ... }
	 }
}
\references{
%%  ~~put references to the literature/web site here~~
}
\author{
Adam Vogt
}
\note{
%%  ~~further notes~~
}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{
%%  ~~objects to See Also as \code{\link{~~fun~~}}, ~~~
%%  ~~or \code{\linkS4class{CLASSNAME}} for links to other classes ~~~
}
\examples{
showClass("rational")
}
\keyword{classes}
