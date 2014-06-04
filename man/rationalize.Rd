\name{rationalize}
\alias{rationalize}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
divide out common factors
}
\description{
divide out common factors
}
\usage{
rationalize(r, tol = 1e-07)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{r}{
  Value in class \link{rational-class}
}
  \item{tol}{
  Zeroes this distance apart or closers (\code{Mod}) are considered to be equal 
}
}
\details{
%%  ~~ If necessary, more details than the description above ~~
}
\value{
  An object of \link{rational-class}
}
\references{
%% ~put references to the literature/web site here ~
}
\author{
%%  ~~who you are~~
}
\note{
%%  ~~further notes~~
}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{
%% ~~objects to See Also as \code{\link{help}}, ~~~
}
\examples{
x <- rational( c(0, 1), c(0, 1) )
rationalize(x)
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
\keyword{ ~kwd1 }
\keyword{ ~kwd2 }% __ONLY ONE__ keyword per line
