# Work Stealing Protocol

~~~~
         m: for (i <- 1..k) { m: x <- recv(); send(x, i) }
         m: for (p <- S) { m: x <- recv(); send(x, DONE) }
||_{p:S} p: while (true) { p: send(m, p); y <- recv(); if y = DONE then break else skip }
~~~~

~~~~
         m: for (i <- 1..k) { m: x <- recv(); send(x, i) }
         m: for (p <- S) { m: x <- recv(); send(x, DONE) }
||\forall(p:S), p: while (true) { p: send(m, p); y <- recv(); if y = DONE then break else skip }

   m: for (i <- 1..k) { m: x <- recv(); send(x, i) }
   m: for (p <- S) { m: x <- recv(); send(x, DONE) }
|| p: for (i <- 1..k) { p: assert true; p:send(m,p); p:y<-recv(); if y = DONE then break else skip; }
   \forall(p:S), p: while (true) { p: send(m, p); y <- recv(); if y = DONE then break else skip }

Obligation:
   m: for (i <- 1..k) { m: x <- recv(); send(x, i) }
   m: for (p <- S) { m: x <- recv(); send(x, DONE) }
|| p: for (i <- 1..k) { p: assert true; p:send(m,p); p:y<-recv(); if y = DONE then break else skip; }
   \forall(p:S), p: while (true) { p: send(m, p); y <- recv(); if y = DONE then break else skip }
~~~~
