# Ping Variants

## Ping "Classic"
~~~~
   m: for (p <- P) { m: send(p, m); }; 
   m: for (p <- P) { m: recv(); }
||_{p:P} p: x <- recv(); p: send(x, p);
~~~~

## Ping "Race"
~~~~
         m: for (p <- P) { m: x <- recv(); m: send(x, m); }; 
||_{p:P} p: send(m, p); p: recv()
~~~~

## Ping "Determined"
~~~~
         m: for (p <- P) { m: send(p, m); }; 
||_{p:P} p: x <- recv(); p: send(x, p);
~~~~
