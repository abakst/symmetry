#Blerg

(send{t}(m,n); P) ↓(S,R)
   | t ∈ R             = send{t}(m,n); P ↓(S,R)
   | t ∉ R             = P ↓(S,R)
(recv{t}(); P) ↓(S,R)
   | t ∈ S             = recv{t}(); P ↓(S,R)
   | t ∉ S             = P ↓(S,R)
(for (e) { P }) ↓(S,R) = for (e) {P ↓(S,R)}
(Πi:I. P)       ↓(S,R) = Πi:I. (P ↓(S,R))
(P || Q) ↓(S,R)        = (P↓(S,R) || Q↓(S,R))

P ↑ (S,R) = P ↓ (comp(S),comp(R))

env(send{t}(m,n);P) = ({t}, ∅) ⊔ env(P)
env(recv{t}(m,n);P) = (∅, {t}) ⊔ env(P)
env(P || Q) = env(P) ⊔ env(Q)

(S,R) ⊔ (S',R') = (S ∪ S, R ∪ R')

G(p) = pid  ∘ ∈ {-,+,◯}
----------------  
G ⊢ p : pid∘

G(p) = pid∘  ∘ ∈ {-,+,◯}
----------------  
G ⊢ p : pid∘


send(p)  = p 
send(p+) = p + 
recv(p)  = p
recv(p-) = p ◯

G ⊢ p : pid+
---------------------------------------------------------------------------- [ send ]
G, p:send{A}(q,e) ~~> G[(p,q) := G(p,q)@e][p := send(p)], skip

G(p,q) = e:M      G ⊢ p : pid-
-------------------------------------------------------------------- [ recv ]
G, q:x <- recv{A}() ~~> G[(p,q) := M, x := e][p := recv(p)], x <- e, skip 

∘ ∈ {-,+}   G ∪ {j̣∘}, (P(i*) || Q(j*))↓env(P,Q) ~~> G', T(i*), Q(i*)↓env(P,Q)
------------------------------------------------------------------------ [ loop-1 ]
G, for (i:I) B || Π(j:J).Q(p) ~~> G', for (i:I) T(i),  (for (i:I) P(i)||(j <- *; Q(j))↑env(P,Q)) || Π(i:I).Q(i)

∘ ∈ {-,+}   G ∪ {ị∘}, P(i*) || Q(i*) ~~> G', T(i*), skip 
------------------------------------------------------------------------ [ loop-2 ]
G, for (i:I) B || Π(i:I).Q(i) ~~> G', for (i:I) T(i), skip 

G, P ↓ env(P) ~~> G', T, skip
------------------------------ [ resid ]
G, P ~~> G', T, P ↑ env(P)
