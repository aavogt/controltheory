\name{rlocus}
\alias{rlocus}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Calculate the root locus of the provided open-loop transfer function
}
\description{
 Given an open-loop transfer function \eqn{N/D}{N/D}, calculate the paths of
 the closed-loop poles (values of \eqn{s}{s} satisfying \eqn{0 = kN + D}{0 = kN + D})
 as the proportional gain \eqn{k}{k} increases from 0.

 Important features such as where poles leave or enter the real axis,
 as well as places where poles cross the imaginary axis are included,
 without needing to guess particular ranges for \eqn{k}{k}.
}
\usage{
rlocus(oltf, eps.im = 1e-08, eps.re = -1e-08, k.def.max = 10, k.expand.f = 1.1, k.offset = 1e-04, ks.override = NULL, isosamples.pole = 20, isosamples.asymptote = 10)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{oltf}{
    Open loop transfer function \eqn{N/D}{N/D}
}
  \item{eps.im}{
    Points this close to the real-axis are considered real for the purposes of finding break-out points.
}
  \item{eps.re}{
    Points within this distance of the imaginary axis are considered marginally stable
}
  \item{k.def.max}{
    Maximum proportional gain to use in the absence of any interesting features (break-out, crossing the imaginary axis)
}
  \item{k.expand.f}{
    Factor to expand the 
}
  \item{k.offset}{
    Paths of poles approach break-out points by this factor
}
  \item{ks.override}{
    Override the gains selected
}
  \item{isosamples.pole}{
    Number of points for poles
}
  \item{isosamples.asymptote}{
    Number of points for asymptotes
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
\references{
%% ~put references to the literature/web site here ~
}
\author{
  Adam Vogt
}
\note{
%%  ~~further notes~~
}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{
%% ~~objects to See Also as \code{\link{help}}, ~~~
}
\examples{
##---- Should be DIRECTLY executable !! ----
##-- ==>  Define data, use random,
##--	or do  help(data=index)  for the standard data sets.

## The function is currently defined as
}
\keyword{ ~kwd1 }
\keyword{ ~kwd2 }% __ONLY ONE__ keyword per line
