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
G, p:send{A}(q,e) ~~> G[(p,q) := G(p,q)@e, p := send(p)], skip

G(p,q) = e:M     G ⊢ p : pid-
-------------------------------------------------------------------- [ recv ]
G, q:x <- recv{A}() ~~> G[(p,q) := M, x := e, p := recv(p)], x <- e, skip 

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
--------------------------------------------------- [ trans ]
G, P ~~> G'', (Tᵢ;Tᵢ', Tₒ;Tₒ', Q)

G, P₀ || Q ~~> G', (Tᵢ, Tₒ, P₁ || Q)
-------------------------------------- [ seq ]
G, P₀;P || Q ~~> G', (Tᵢ, Tₒ, P₁;P || Q)


G, P ~~> G', (Tᵢ, Tₒ, skip)
-------------------------- [ intern ] 
G, P --> G', ({Tᵢ}, Tₒ)

G, P --> G', (Tᵢ, Tₒ)
G', Q || Tₒ --> G'', (Tᵢ', Tₒ')
-------------------------------- [ residual ]
G, P || Q --> G'', (Tᵢ ∪ Ti', Tₒ')


G, P --> 


G, P ~~> G', (Δᵢ, Δₒ, Q) 