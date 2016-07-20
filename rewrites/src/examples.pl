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
           For-loops:
====================================*/

/*===========
Simple ping
===========*/

rewrite_query(T, Ind, Name) :-
	Ind=[], 
	P1=seq([send(m,e_pid(Q),m), recv(m,x)]),
	P2=seq([recv(P, id),send(P,e_pid(m),P)]),
	T=(par([for(m, Q, s, P1), sym(P, s, P2)])),
	Name='simple ping loop'.


/*===========
Reverse ping
===========*/

rewrite_query(T, Ind, Name) :-
	Ind=[], 
	P1=seq([recv(m,id), send(m,e_var(id),m)]),
	P2=seq([send(P,e_pid(m),P), recv(P, x)]),
	T=(par([for(m, _, s, P1), sym(P, s, P2)])),
	Name='reverse ping'.

/*===========
 Two loops
===========*/

rewrite_query(T, Ind, Name) :-
	Ind=[], 
	P1A=seq([send(m,e_pid(Q),m)]),
	P1B=seq([recv(m,x)]),
	P2=seq([recv(P, id),send(P,e_pid(m),P)]),
	T=(par([seq([for(m, Q, s, P1A),for(m, Q, s, P1B)]), sym(P, s, P2)])),
	Name='two loops'.

/*============
Two loops var
===============*/

rewrite_query(T, Ind, Name) :-
	Ind=[], 
	P1A=seq([send(m,e_pid(Q), m)]),
	P1B=seq([recv(m, x)]),
	P2=seq([recv(P, id), send(P,e_var(id),P)]),
	T=(par([for(m, Q, s, P1A), for(m, Q, s, P1B), sym(P, s, P2)])),
	Name='two loops var'.

/*===========
 Double ping:
===========*/
rewrite_query(T, Ind, Name) :-
	Ind=[], 
	P1=seq([send(m,e_pid(Q),m),send(m,e_pid(Q),m),recv(m,id1),recv(m,id2)]),
	P2=seq([send(P,e_pid(m),P),send(P, e_pid(m), P), recv(P, x1), recv(P, x2)]),
	T=(par([for(m, Q, s, P1), sym(P, s, P2)])),
	Name='double ping'.

/*===========================================
           Nondet/ Iter-loops / while loops:
===========================================*/

rewrite_query(T, Ind, Name) :-
	Ind=[],
	P1=nondet(P, send(P, e_pid(m), v)),
	P2=recv(m, v),
	T=(par([P1, P2])),
	Name='nondet'.


rewrite_query(T, Ind, Name) :-
	Ind=[],
	P1=nondet(P, send(P, e_pid(m), P)),
	P2=seq([recv(m, v)]),
	T=(par([iter(env, k, P1), iter(m, k, P2)])),
	Name='iter-simple'.

rewrite_query(T, Ind, Name) :-
	Ind=[],
	P1=seq([recv(q, id), send(q, e_var(id), 1)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([send(P, e_pid(q), P), recv(P, stop)])),
	T=(par([for(q, _, s, P1), sym(P, s, P2)])),
	Name='work-stealing 2nd-phase'.


rewrite_query(T, Ind, Name) :-
	Ind=[],
	P1A=seq([recv(q, id), send(q, e_var(id), 0)]),
	P1B=seq([recv(q, id), send(q, e_var(id), 1)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([send(P, e_pid(q), P), recv(P, stop)])),
	T=(par([seq([iter(q, k, P1A), for(q, _, s, P1B)]), sym(P, s, P2)])),
	Name='work-stealing'.

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
	 T=(par([for(m, Q, s, P1), sym(P, s, P2), for(m, _, s, P3)])),
	Name='two-party ping'.

/*=========================
Interleaved two-party ping
==========================*/

rewrite_query(T, Ind, Name) :-
	Ind=[(m,n)],
	P1=seq([recv(m, id), send(m, e_var(id), m)]),
	P2=seq([send(P, e_pid(m), P), send(P, e_pid(n), P), recv(P, id)]),
	P3=seq([recv(n, x)]),
	T=(par([for(m, _, s, P1), sym(P, s, P2), for(n, _, s, P3)])),
	Name='interleaved two-party ping'.

/*=========================
        Map-reduce
==========================*/

rewrite_query(T, Ind, Name) :-
	Ind=[(q,m)],
	P1A=seq([recv(q, id), send(q, e_var(id), 0)]),
	P1B=seq([recv(q, id), send(q, e_var(id), 1)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([send(P, e_pid(q), P), recv(P, stop),
				if(P, stop=0, send(P, e_pid(m), P))])),
	P3=seq([recv(m, id)]),
	T=(par([seq([iter(q, k, P1A), for(q, _, s, P1B)]), sym(P, s, P2), iter(m, k, P3)])),
	Name='map-reduce'.

/*=============================
        If-then-else
=============================*/


firewall(T, Delta1, Rho1) :-
	init_independent([(sv, s)]),
	empty_avl(Gamma),
	empty_avl(Rho),
	empty_avl(Psi),
	Delta=[],
	Server=seq([
		    recv(sv,  pair(id, msg)),
		    ite(msg=\=bad, send(sv, e_var(id), msg), skip)
		   ]),
	Firewall=seq([
		      recv(fw, pair(id, msg)),
		      ite(
			  msg=bad,
			  send(fw, id, wrong-message),
			  seq([
			       send(fw, e_pid(sv), pair(fw, msg)),
			       recv(fw, sv, retmsg),
			       send(fw, e_pid(id), retmsg)
			      ])
			 )
		     ]),
	Client=seq([send(P, fw, pair(P, n)), recv(P, ret)]),
	T=( par([
		 while(sv, true, Server),
		 while(fw, true, Firewall),
		 sym(P, s, Client)
		])
	  ),
	rewrite(T, Gamma, Delta, Rho, Psi,
		par([while(sv, true, Server), while(fw, true, Firewall)]),
		_, Delta1, Rho1, Psi).

concdb(T, Delta1, Rho1) :-
	init_independent([(q,m)]),
	empty_avl(Gamma),
	empty_avl(Rho),
	empty_avl(Psi),
	Delta=[],
	DB=seq([
		recv(db, pair(act, id)),
		ite(act=alloc, AllocDB, LookupDB)
	       ]),
	AllocDB = ite(
		     ndet, seq([send(db, e_var(id), free), recv(db, v1)]),
		     send(db, e_var(id), alloc)
		    ),
	LookupDB = send(db, e_var(id), val),
	Client=seq([
		ite(ndet, assign(P, act, lookup), assign(P, act, alloc)),
		send(P, db, pair(act,P)),
		ite(act=alloc, AllocC, LookupC)
	       ]),
	AllocC= seq([
		     recv(P, msg),
		     ite(msg=free, send(P, e_pid(db), v3), skip)
		    ]),
	LookupC= recv(P, val),
	T=(par([while(db, true, DB), sym(P, s, Client)])),
	rewrite(T, Gamma, Delta, Rho, Psi, while(db, true, DB), _, Delta1, Rho1, Psi).

