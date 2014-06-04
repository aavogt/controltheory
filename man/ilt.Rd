\name{ilt}
\alias{ilt}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Numerical inverse Laplace transform
}
\description{
  Calculates the time domain values of a signal given it's
  Laplace transform.
}
\usage{
ilt(num, den, times=seq(10))
ilt(rational(num, den), times=seq(10))
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{num}{
    Numerator coefficients in ascending order.
}
  \item{den}{
    Denominator coefficients in ascending order.
}
  \item{\dots}{
    Arguments passed on to \code{\link{radau}}.
}
}
\details{
%%  ~~ If necessary, more details than the description above ~~
}
\value{
%%  ~Describe the value returned
%%  If it is a LIST, use
%%  \item{comp1 }{Description of 'comp1'}
%%  \item{comp2 }{Description of 'comp2'}
%% ...
}
\author{
Adam Vogt
}
\note{
%%  ~~further notes~~
}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{
\code{\link{rationalize}}
}
\examples{
##---- Should be DIRECTLY executable !! ----
##-- ==>  Define data, use random,
##--	or do  help(data=index)  for the standard data sets.
}
