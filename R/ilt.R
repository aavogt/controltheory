
uniq.sort.approx <- function(x, tolerance=1e-5) if (length(x) == 0) x else {
  sx <- sort(x)
  for (i in 2:length(sx)) {
    if ( abs(sx[i] - sx[i-1]) < tolerance)
      sx[i-1] <- NA
  }
  sx[ ! is.na(sx) ]
}

nn2.reorder <- function(a,b) {
    nnab <- nn2( a, b)
    for (j in seq(2, nrow(nnab$nn.idx))) {
      while( any(nnab$nn.idx[ j, 1 ] == nnab$nn.idx[ 1:(j-1), 1 ]) ) {
        nnab$nn.idx[ j, ] <- c(tail(nnab$nn.idx[j, ], -1), NA)
      }
    }
    nnab$nn.idx[ , 1]
}

dropLeadingZeros <- function(x) {
  zs <- which(x == 0)
  if (length(zs) == 0) as.numeric(x) else
    x[ ! which( zs == seq_along(zs)) ]
}

toDescCoefs <- function(x)
    list( polynomial = rev(as.numeric(x)),
          numeric = rev(x) ) [[class(x)]]


rational <- function(num, den) {
  r <- list(num=as.polynomial(num), den=as.polynomial(den))
  class(r) <- 'rational'
  r
}

as.rational.polynomial <- function(n) rational(n, 1)
as.rational.numeric <- function(n) rational(as.polynomial(n), 1)

rationalize <- function(r, tol=1e-7) {
  nz <- polyroot(r$num)
  dz <- polyroot(r$den)

  if (length(r$num) <= 1 | length(r$den) <= 1) r else {
    fac <- tail( as.numeric( r$num ), 1) / tail( as.numeric( r$den ), 1)

    for (i in seq_along(nz))
      for (j in seq_along(dz))
        if (!is.na(dz[j]) & !is.na(nz[i]) & Mod( dz[j] - nz[i] ) < tol) {
            dz[j] <- NA
            nz[i] <- NA
        }

    # poly from zeros warns about discarding what are
    # practically very negligible complex numbers
    pfz <- function(x) {
      p <- 1
      for (xi in x) p <- c(0, p) - c(xi * p, 0)
      if (!isTRUE( all.equal( Im(p), rep(0, length(p) ) ) )) {
      warning('rationalize discards meaningful Im')
      }
      polynomial(Re(p))
    }
    rational( pfz(nz[ !is.na(nz) ]) * fac,
              pfz(dz[ !is.na(dz) ]) )
  }
}

`/.rational` <- function(a,b) rational(a$num*b$den, a$den*b$num)
`+.rational` <- function(a,b) rational(a$num*b$den + b$num*a$den, a$den * b$den) 
`-.rational` <- function(a,b) rational(a$num*b$den - b$num*a$den, a$den * b$den) 
`*.rational` <- function(a,b) rational(a$num*b$num, a$den*b$den)

print.rational <- function(x, oneLine = F, ...) {
  n <- as.character(x$num)
  d <- as.character(x$den)
  invisible(cat(
    if (oneLine) paste(n, '/', d)
    else {
      bar <- paste0(rep('-', max(nchar(n), nchar(d))), collapse='')
      paste( n, bar , d, sep='\n')
    }, '\n'))
}

where.pos <- function(a) {
  a <- rationalize(a)
  n <- polyroot(a$num)
  d <- polyroot(a$den)
  v <- rle( sort( c(Inf, -Inf, n, d) ) )
  v <- Re( v$values[ v$lengths %% 2 == 1 & (abs(Im(v$values)) < 1e-10) ] )
  ppV <- levels( cut( 0, v ) )

  # one negative when we have an odd degree (x^3, x^5  ...)
  # one negative for each negative coefficient on the highest power
  negInfSign <- sign(prod(sapply( a[ c('num', 'den') ], function(x)
                            tail(x, 1) * # coef
                            (0.5 - (length(x) %% 2 == 1)) # degree
                            )))
  list(pp =
  data.frame(
      v = ppV,
      sign = rep( negInfSign *c(1, -1), length.out=length(ppV)),
      stringsAsFactors = F),
    dat = v,
    signExtreme = tail(a$num, 1),
    term = a)

}

where.pos.all <- function(a) {
  pts <- mdply( 1:length(a), function(i) {
               data.frame(p=head(a[[i]]$dat, -1), sign = a[[i]]$pp$sign)
    })
  ps <- unique(sort(pts$p))
  pts <- ddply( pts, .(X1), function(x)
               within( x[ findInterval( ps, x$p) ,  ],
                      p2 <- ps) )
  ints <- dcast(pts, 1 ~ p2, min, value.var='sign', fill=Inf)[ , -1]
  sgn <- as.numeric(ints[ 1, ])
  sgn.rle <- rle(sgn)
  dropIx <- cumsum(sgn.rle$lengths)[ sgn.rle$lengths > 1 ]
  dropIx <- if (length(dropIx) == 0) T else -dropIx

  cuts <- c(as.numeric(colnames(ints)), Inf)[ dropIx ]
  ppInts <- levels( cut(0, cuts ))

  list( pp = data.frame( ppInts, sign =sgn[ dropIx]  ),
        cuts = cuts)
}

routh_array <- function(num, den) {
  den <- toDescCoefs(den)
  num <- toDescCoefs(num)

  lenMax <- max( length(den),  length(num))

  nc <- ceiling( lenMax /2 )

  pad <- function(x) {
    coeffs <- c(rep(0, lenMax - length(x)), as.numeric(x))
    if (lenMax %% 2 == 1) coeffs <- c(coeffs, 0)
    coeffs
  }
  den <- pad(den)
  num <- pad(num)

  M <- vector('list', nc*2)

  for (i in seq_along(M))
    M[[i]] <- rational( c(den[i], num[i]), 1)

  M <- matrix(M, ncol=nc)

  m <- function(i,j) if (j > nc) 0 else M[[i, j]]

  addEntry <- function(i,j) {
    M[[i,j]] <<-  if (!isTRUE( all.equal( m(i-1, j)$num, 0 ) ))
          m(i-2, j+1) - m(i-2, j)*m(i-1, j+1)/m(i-1, j)
      else { warning('addEntry'); 0 }
  }

  addRow <- function() {
    M <<- rbind(M, as.list(rep(list(rational(0, 1)), nc)))
    for (j in seq(ncol(M)-1)) addEntry(nrow(M), j)
  }
  for (i in seq(ncol(M) - nrow(M) + 1)) addRow()


  lapply( 1:nrow(M), function(i) M[[i, 1 ]])

}

stable.intervals <- function(num, den)
  where.pos.all( lapply( routh_array( num, den ), where.pos) )

ilt <- function(num, den, ...) {

  num <- toDescCoefs(num)
  den <- toDescCoefs(den)

  makeMass <- function(ps) {
    m <- diag(length(ps)-1)
    m[1, ] <- head(ps, -1)
    m
  }

  M <- makeMass(den / den[1])

  y0 <- solve(M, rev(c(rep(0, length(den) - 1 - length(num)), num) / den[1]))

  if (length(den) <= 2)
      func <- function(t,y,p)
        list( c( - tail(den, 1) * y[length(den)-1]))
    else
      func <- function(t,y,p)
        list( c( - tail(den, 1) * y[length(den)-1] / den[1],
                  head(y, -1) ))

  r <- radau(y = y0,
        mass = M,
        func = func,
        rootfunc = function(t,y,p) if (tail(y, 1) > 0.1) tail(y, 2)[1] else 1,
        events = list(root=T, terminalroot = F),
        ...)

  colnames(r)[length(colnames(r))] <- 'y'
  colnames(r)[ 2 : (ncol(r)-1) ] <- paste0('dy.', seq(ncol(r)-2, 1, by=-1))
  r
}

# evaluates a ratio of polynomials a/b at x
lhopitalRat <- function(x, a, b) {
  result <- NaN
  while (length(b) > 0) {
    va <- as.function(a)(x)
    vb <- as.function(b)(x)
    if (va != 0 & vb != 0) {
      result <- va/vb
      break
    }
  }
  result
}

rlocus <- function(num, den,
                   eps.im = 1e-8,
                   eps.re = -1e-8,
                   k.def.max = 10,
                   k.expand.f = 1.1,
                   k.offset = 1e-4,
                   ks.override = NULL,
                   isosamples.pole = 20,
                   isosamples.asymptote = 10) {
  num <- polynomial(num)
  den <- polynomial(den)

  breakOut <- deriv(num) * den - num * deriv(den)
  breakOuts <- polyroot(breakOut)
  breakOuts <- do.call('rbind', lapply( breakOuts, function(s)
    data.frame(s=s, k= - as.vector(lhopitalRat(s, den, num)))
    ))
  breakOuts <- subset(breakOuts, abs(Im(k)) < eps.im & Re(k) > 0 & Im(s) < eps.im)
  dsdk <- function(k, y, parms) {
    s <- complex(real=y[1], imaginary=y[2])
    n <- as.function(num)(s)
    dn <- as.function(deriv(num))(s)
    dd <- as.function(deriv(den))(s)
    r <- - n / (k*dn + dd)
    list( c(Re(r), Im(r)) )
  }
  poles <- polyroot(den)

  ks.stable <- stable.intervals( num, den )
  
  ks <- if (!is.null(ks.override)) ks.override else
    sort( c( k.def.max, Re(breakOuts$k),
                 { sc <- ks.stable$cuts
                   sc[ !is.infinite(sc) & sc > 0 ] }))

  if (max(ks) > k.def.max) ks <- c(ks, max(ks)* k.expand.f)

  # solve the DE  ds/dk = N / (k N' + D' ),
  # which comes from differentiating the characteristic
  # polynomial kN + D with respect to k
  r <- mlply( data.frame(k.low=c(0, head(ks, -1)),
                         k.high=ks),
             function(k.low, k.high) {

    dk <- (k.high-k.low)*k.offset

    ps <- polyroot( (k.low+dk)*num + den )

    runSolver <- function(times, p) {
        lsodar(
          c(Re=Re(p), Im=Im(p)),
          times,
          dsdk,
          list(),
          rootfunc = function(t, y, p) y[1],
          events = list(root=T, terminalroot=F) )
    }

    defTimes <- seq(k.low+dk, k.high - dk, length.out=isosamples.pole)

    sol1s <- llply( ps, function(p) runSolver(defTimes, p))
    troots <- uniq.sort.approx(c(lapply(sol1s, attr, 'troot'), recursive=T))

    # crossings into the RHP show up as troot, re-run the solver
    # with values very close on either side (by k.offset)
    if (is.null(troots)) sol1s else {
      newTimes <- sort(c(defTimes, 
                         c(outer(troots,
                                 c(1, -1)*(k.high-k.low)*k.offset,
                                  FUN='+'))))
      llply( ps, function(p) runSolver(newTimes, p))
    }
  })
  names(r) <- 1:length(r)

  # should be null
  crossings <-
    uniq.sort.approx(
    c( mlply(seq_along(r), function(i)
            c(lapply(r[[i]], attr, 'troot'), recursive=T)),
          recursive=T)
    )

  if (length(r) >= 2) {

    # r[[i+1]] poles when k = k.low are sorted to be close the poles
    # in r[[i]] when k = k.high
    for (i in 2:length(r)) {

      # in the ii'th group (by runs of 'k' broken up by breakpoints)
      # get a matrix with Re and Im columns. The rows are locations
      # of different poles (from the fnN'th row --- usually the first
      # or last)
      grabRi <- function(ii, fnN = tail) t(
        sapply( r[[ii]], function(x) tail( c(fnN(x, 1)) , -1)))

      r[[i]][ nn2.reorder( grabRi(i-1, tail), grabRi(i, head)) ] <- r[[i]]
    }
  }


  nRoots <- polyroot(num)
  dRoots <- polyroot(den)
  nAsymptotes <- length(dRoots) - length(nRoots)
  centroid <- (sum(Re(dRoots)) - sum(Re(nRoots))) / nAsymptotes

  asymptotes <- exp( complex(real=rep(0,nAsymptotes),
                             imaginary = - 2*((1 : nAsymptotes)  + 0.5) * pi / nAsymptotes)) *
      sqrt( sum( sapply(r[[length(r)]], function(x) with(data.frame(tail(x, 1)), Im^2 + Re^2 ) ))
           - sum( Mod(nRoots)^2) ) * 2 / nAsymptotes + centroid

  a <- t(sapply( r[[length(r)]], tail, 1))[ , 2:3 ]
  b <- cbind(Re(asymptotes), Im(asymptotes))
  asymptotePoles <- nn2.reorder( a, b)

  r <- dcast(melt(r), ... ~ Var2 )
  names(r) <- c('k.idx', 'pole', 'k.int.idx', 'Im', 'Re', 'k')
  r$pole <- factor(r$pole)
  r <- r[ order(r$k), ]

  posOnly <- function(x) x[ x >= 0 & !is.infinite(x) ]
  r$k.int <- cut(r$k, posOnly( c(0, crossings, ks.stable$cuts, max(ks))),
                 include.lowest=T)
  r <- ddply(r, .(k.int), function(x)  {
             mRe <-  max(x$Re)
             s <- if (mRe > eps.re) 'unstable' else
               if (mRe < -eps.re) 'stable' else 'marginally stable'
             within(x, stability <- s )
  })

  asymps <- mdply( data.frame( f = 0 : isosamples.asymptote /
                                          isosamples.asymptote ), function(f) {
    v <- (asymptotes - centroid) * f + centroid
    data.frame( # k = f * max(ks),
                pole = factor(as.character(asymptotePoles), as.character(levels(r$pole))),
                Re = Re(v),
                Im = Im(v)) })

  list( poles = r,
        asymptotes = asymps[ order( asymps$f, asymps$pole) , ],
        points = {
          rbind(
            data.frame(type = rep('z', length(nRoots)), Re = Re(nRoots), Im = Im(nRoots)),
            data.frame(type = rep('p', length(dRoots)), Re = Re(dRoots), Im = Im(dRoots)),
            data.frame(type = 'centroid', Re = centroid, Im = 0)
          )
        },
        ks.stable = ks.stable)

}

p <- function(...) if (length(c(...)) == 0) polynomial() else polynomial( c(...) )
