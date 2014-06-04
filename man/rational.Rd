\name{rational}
\alias{rational}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Constructor for \code{\link{rational-class}}
}
\description{
%%  ~~ A concise (1-5 lines) description of what the function does. ~~
}
\usage{
rational(num, den = 1)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{num}{
  numerator
}
  \item{den}{
  denominator
}
}
\seealso{
\code{\link{polynomial}}, \code{\link{rational-class}}
}
\examples{
##---- Should be DIRECTLY executable !! ----
##-- ==>  Define data, use random,
##--	or do  help(data=index)  for the standard data sets.

## The function is currently defined as
function (num, den = 1) 
{
    new("rational", num = as.polynomial(num), den = as.polynomial(den))
  }
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
\keyword{ ~kwd1 }
\keyword{ ~kwd2 }% __ONLY ONE__ keyword per line
