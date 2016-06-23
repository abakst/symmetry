send(p)  = p 
send(p+) = p + 

recv(p)  = p
recv(p-) = p ◯

G(p) = pid  ∘ ∈ {-,+,◯}
----------------  
G ⊢ p : pid∘

G(p) = pid∘  ∘ ∈ {-,+,◯}
----------------  
G ⊢ p : pid∘

ctx(send{t}(m,n);P) = ({t}, ∅) ⊔ ctx(P)
ctx(recv{t}(m,n);P) = (∅, {t}) ⊔ ctx(P)
ctx(P || Q) = ctx(P) ⊔ ctx(Q)

ctx(x) ⊓ ctx(Q) = ∅
---------------------------
⊢ i ▹ x : ext Q

G ⊢ p : pid+
-------------------------------------------------------------- [ send ]
G, p:send{A}(q,e) ~~> G[(p,q) := G(p,q)@e][p := send(p)], skip

G(p,q) = e:M     G ⊢ p : pid-
-------------------------------------------------------------------- [ recv ]
G, q:x <- recv{A}() ~~> G[(p,q) := M, x := e][p := recv(p)], x <- e, skip 

⊢ i ▹ x : ext Q
-------------------------------------------------------------------- [ extern ]
G, i ▹ x; P || Q ~~> G, (skip, i ▹ x, Q)

∘ ∈ {-,+}
G ∪ {i∘}, P(i*) || Q(i*) ~~> G', (Tᵢ, Tₒ, skip)
------------------------------------------------------------------------ [ loop-1 ]
G, for (i:I) B || Π(i:I).Q(p) ~~> G', (for (i:I) Tᵢ, for (i:I) Tₒ, skip)

∘ ∈ {-,+}
G ∪ {i∘}, P(i*) || Q(i*) ~~> G', (Tᵢ, Tₒ, Q(i*))
------------------------------------------------------------------------- [ loop-2 ]
G, for (x:X) P || Π(i:I).Q(i) ~~> G', (for (x:X) Tᵢ, for(x:X) Tₒ, Π(i:I).Q(i))

G, P ~~> G', (Tᵢ, Tₒ, P')    G', P' ~~> (Tᵢ', Tₒ', Q)
------------------------------------------------------------------------- [ trans ]
G, P ~~> G'', (Tᵢ;Tᵢ', Tₒ;Tₒ', Q)

G, P ~~> G', (Tᵢ, Tₒ, skip)
--------------------------------------
G, P --> G', ({Tᵢ}, Tₒ)

G, P --> G', (Tᵢ, Tₒ)
G', Q || Tₒ --> G'', (Tᵢ', Tₒ')
--------------------------------
G, P || Q --> G', (Tᵢ ∪ Ti', Tₒ')


# But does it float?

       m1: for (p : P) send(p,1);
    || m2: for (p : P) m2.x <- recv();
    || Π(p:P). p.x <- recv(); send(m2,1);

    send(p*,1) || p*: p*.x <- recv(); send(m2, 1)
      ~~> (p*.x = 1, send(m2,1), -)
    -------------------------------------------------------------
    m1: for (p : P) send(p,1); || Π(p:P). recv(); send(m2,1);
      ~~> (for (p : P) p.x = 1, for (p : P) send(m2, 1), -)
    -------------------------------------------------------------
    m1: for (p : P) send(p,1); || Π(p:P). recv(); send(m2,1);
      --> (for (p : P) p.x = 1, for (p : P) send(m2, 1))

    send(m2, 1) || m2.x <- recv(); ~~> (m2.x <- 1, -, -)
    -------------------------------------------------------------
    for (p : P) send(m2, 1) || m2 : for (p : P) m2.x <- recv();
      ~~> (for (p : P) m2.x <- 1, -, -)
    -------------------------------------------------------------
    for (p : P) send(m2, 1) || m2 : for (p : P) m2.x <- recv();
      --> (for (p : P) m2.x <- 1, -)


    m1: for (p : P) send(p,1); || Π(p:P). recv(); send(m2,1);
      --> (for (p : P) p.x <- recv(), for (p : P) send(m2, 1))
    for (p : P) send(m2, 1) || m2 : for (p : P) m2.x <- recv();
      --> (for (p : P) m2.x <- 1, -)
    -------------------------------------------------------------
       m1: for (p : P) send(p,1);
    || m2: for (p : P) m2.x <- recv();
    || Π(p:P). p.x <- recv(); send(m2,1);
    --> ({for (p : P) p.x <- 1, for (p : P) m2.x <- 1}, -)