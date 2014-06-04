.onLoad <- function(libname, pkgname) {
  setClass('polynomial', representation('numeric'))
  setClass('rational', representation(num='polynomial', den='polynomial'))

  for (sigA in c('rational', 'polynomial', 'numeric')) {
  for (sigB in c('rational', 'polynomial', 'numeric')) {
      if ('rational' %in% c(sigA, sigB)) {
        setMethod('Arith',
            signature(e1 = sigA, e2 = sigB),
            function(e1,e2) {
              i <- match(as.character(.Generic), names(rationalOps))
              rationalOps[[i]](as.rational(e1), as.rational(e2))
            })
  }}}

  setMethod('print', 'rational', print.rational)
  setMethod('as.rational', 'rational', as.rational.rational)
  setMethod('as.rational', 'numeric', as.rational.numeric)
  setMethod('as.rational', 'polynomial', as.rational.polynomial)
  setMethod('show',signature(object='rational'),
            function(object) print.rational(object))
}

