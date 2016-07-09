/*====================================
           Loop free:
====================================*/

/*===========
"Single ping":
===========*/

rewrite_query(T, Ind, Name) :-
	Ind=[],
	P1=seq([send(m,e_pid(p),m), recv(m, x1)]),
	P2=seq([recv(p, id), send(p,e_var(id),p)]),
	T=(par([P1,P2])), Name='single ping'.

/*===========
"Send first":
===========*/

 rewrite_query(T, Ind, Name) :-
	 Ind=[], 
	 P1=seq([send(p0,e_pid(p1),p0),recv(p0,x1)]),
	 P2=seq([send(p1, e_pid(p0), p1), recv(p1,x1)]),
	 T=(par([P1,P2])), Name='send first'.

/*===========
"Registry":
===========*/

rewrite_query(T, Ind, Name) :-
	Ind=[], 
	M=seq([send(m,e_pid(p1),r),send(m,e_pid(p2),r),recv(m,x1),send(m,e_pid(r),m)]),
	R=seq([recv(r, x1),recv(r, x2),send(r,e_pid(m),a),recv(r, x3)]),
	P1=seq([recv(p1, x1),send(p1,e_var(x1),p1)]),
	P2=seq([recv(p2, x1),send(p2,e_var(x1),p2)]),
	T= par([M,R,P1,P2]), Name='registry'.

/*====================================
                Loops:
====================================*/

/*===========
Simple ping
===========*/

rewrite_query(T, Ind, Name) :-
	Ind=[], 
	P1=seq([send(m,e_pid(Q),m),recv(m,x)]),
	P2=seq([recv(P, id),send(P,e_pid(m),P)]),
	T=(par([for(Q, s, P1), sym(P, s, P2)])),
	Name='simple ping loop'.


/*===========
Reverse ping
===========*/

rewrite_query(T, Ind, Name) :-
	Ind=[], 
	P1=seq([recv(m,id), send(m,e_var(id),m)]),
	P2=seq([send(P,e_pid(m),P), recv(P, x)]),
	T=(par([for(_, s, P1), sym(P, s, P2)])),
	Name='reverse ping'.

/*===========
 Two loops
===========*/

rewrite_query(T, Ind, Name) :-
	Ind=[], 
	P1A=seq([send(m,e_pid(Q),m)]),
	P1B=seq([recv(m,x)]),
	P2=seq([recv(P, id),send(P,e_pid(m),P)]),
	T=(par([seq([for(Q, s, P1A),for(Q, s, P1B)]), sym(P, s, P2)])),
	Name='two loops'.

/*============
Two loops var
===============*/

rewrite_query(T, Ind, Name) :-
	Ind=[], 
	P1A=seq([send(m,e_pid(Q), m)]),
	P1B=seq([recv(m, x)]),
	P2=seq([recv(P, id), send(P,e_var(id),P)]),
	T=(par([for(Q, s, P1A), for(Q, s, P1B), sym(P, s, P2)])),
	Name='two loops var'.

/*===========
 Double ping:
===========*/
rewrite_query(T, Ind, Name) :-
	Ind=[], 
	P1=seq([send(m,e_pid(Q),m),send(m,e_pid(Q),m),recv(m,id1),recv(m,id2)]),
	P2=seq([send(P,e_pid(m),P),send(P, e_pid(m), P), recv(P, x1), recv(P, x2)]),
	T=(par([for(Q, s, P1), sym(P, s, P2)])),
	Name='Double ping'.


/*====================================
        Multiple processes:
====================================*/

/*============
Two-party ping
 =============*/
rewrite_query(T, Ind, Name) :-
	 Ind=[], 
	 P1=seq([send(m, e_pid(Q), m)]),
	 P2=seq([recv(P, id), send(P,e_pid(n), P)]),
	 P3=seq([recv(n, x)]),
	 T=(par([for(Q, s, P1), sym(P, s, P2), for(_, s, P3)])),
	Name='two-party ping'.

/*=========================
Interleaved two-party ping
==========================*/

rewrite_query(T, Ind, Name) :-
	Ind=[(m,n)],
	P1=seq([recv(m, id), send(m, e_var(id), m)]),
	P2=seq([send(P, e_pid(m), P), send(P, e_pid(n), P), recv(P, id)]),
	P3=seq([recv(n, x)]),
	T=(par([for(_, s, P1), sym(P, s, P2), for(_, s, P3)])),
	Name='interleaved two-party ping'.
