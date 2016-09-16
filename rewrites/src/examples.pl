
/*===========================================
Examples specified as queries of the form

   rewrite_query(T, Rem, Ind, Name).

- T    : Term to be rewritten
- Rem  : Expected remainder term.
- Ind  : List of pairs of independent processes.
- Name : Example name.
===========================================*/


/*==============
 Loop free:
================*/

/*===========
"Single ping":
===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=seq([send(m,e_pid(p),m), recv(m, x1)]),
	P2=seq([recv(p, id), send(p,e_var(id),p)]),
	T=(par([P1,P2])), Name='single ping'.

/*===========
"Send first":
===========*/

 rewrite_query(T, skip, Ind, Name) :-
	 Ind=[], 
	 P1=seq([send(p0,e_pid(p1),p0),recv(p0,x1)]),
	 P2=seq([send(p1, e_pid(p0), p1), recv(p1,x1)]),
	 T=(par([P1,P2])), Name='send first'.

/*===================
"Registry 2proc":
====================*/
/*
--contains a race.
rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	M=seq([send(m,e_pid(p1),r),send(m,e_pid(p2),r),recv(m,x1),send(m,e_pid(r),m)]),
	R=seq([recv(r, x1),recv(r, x2),send(r,e_pid(m),a),recv(r, x3)]),
	P1=seq([recv(p1, x1),send(p1,e_var(x1),p1)]),
	P2=seq([recv(p2, x1),send(p2,e_var(x1),p2)]),
	T= par([M,R,P1,P2]), Name='registry 2-proc'.
*/
/*==============
  For-loops:
==============*/

/*===========
Simple ping
===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1=seq([send(m,e_pid(Q),m), recv(m,x)]),
	P2=seq([recv(P, id),send(P,e_pid(m),P)]),
	T=(par([for(m, Q, s, P1), sym(P, s, P2)])),
	Name='simple ping loop'.

/*===========
Reverse ping
===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1=seq([recv(m,id), send(m,e_var(id),m)]),
	P2=seq([send(P,e_pid(m),P), recv(P, x)]),
	T=(par([for(m, _, s, P1), sym(P, s, P2)])),
	Name='reverse ping'.

/*===========
 Two loops
===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1A=seq([send(m,e_pid(Q),m)]),
	P1B=seq([recv(m,x)]),
	P2=seq([recv(P, id),send(P,e_pid(m),P)]),
	T=(par([seq([for(m, Q, s, P1A),for(m, Q, s, P1B)]), sym(P, s, P2)])),
	Name='two loops'.

/*============
Two loops var
===============*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1A=seq([send(m,e_pid(Q), m)]),
	P1B=seq([recv(m, x)]),
	P2=seq([recv(P, id), send(P,e_var(id),P)]),
	T=(par([for(m, Q, s, P1A), for(m, Q, s, P1B), sym(P, s, P2)])),
	Name='two loops var'.

/*===========
 Double ping:
 ===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1=seq([send(m,e_pid(Q),m),send(m,e_pid(Q),m),recv(m,id1)]),
	P2=seq([send(P,e_pid(m),P), recv(P, x1), recv(P, x2)]),
	T=(par([for(m, Q, s, P1), sym(P, s, P2)])),
	Name='double ping'.

/*================================
Nondet/ Iter-loops / while loops:
==================================*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=nondet(P, send(P, e_pid(m), v)),
	P2=recv(m, v),
	T=(par([P1, P2])),
	Name='nondet'.


rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=nondet(P, send(P, e_pid(m), P)),
	P2=seq([recv(m, v)]),
	T=(par([iter(env, k, P1), iter(m, k, P2)])),
	Name='iter-simple'.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=seq([recv(q, id), send(q, e_var(id), 1)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([send(P, e_pid(q), P), recv(P, stop)])),
	T=(par([for(q, _, s, P1), sym(P, s, P2)])),
	Name='work-stealing 2nd-phase'.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1A=seq([recv(q, id), send(q, e_var(id), 0)]),
	P1B=seq([recv(q, id), send(q, e_var(id), 1)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([send(P, e_pid(q), P), recv(P, stop)])),
	T=(par([seq([iter(q, k, P1A), for(q, _, s, P1B)]), sym(P, s, P2)])),
	Name='work-stealing'.

/*==================
Multiple processes:
====================*/

/*============
Two-party ping
=============*/

rewrite_query(T, skip, Ind, Name) :-
	 Ind=[], 
	 P1=seq([send(m, e_pid(Q), m)]),
	 P2=seq([recv(P, id), send(P,e_pid(n), P)]),
	 P3=seq([recv(n, x)]),
	 T=(par([for(m, Q, s, P1), sym(P, s, P2), for(m, _, s, P3)])),
	Name='two-party ping'.

/*=========================
Interleaved two-party ping
==========================*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[(m,n)],
	P1=seq([recv(m, id), send(m, e_var(id), m)]),
	P2=seq([send(P, e_pid(m), P), send(P, e_pid(n), P), recv(P, id)]),
	P3=seq([recv(n, e_pid(s), x)]),
	T=(par([for(m, _, s, P1), sym(P, s, P2), for(n, _, s, P3)])),
	Name='interleaved two-party ping'.

/*===========================
  Smaller tests geared
  towards specific rules
=============================*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	T=(par([send(q, e_pid(p), pair(p, test)), recv(p, pair(id,m))])),
	Name='simple pair'.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	T=(par([send(q, e_pid(p), pair(p, test)), recv(p, e_pid(q), pair(id,m))])),
	Name='simple receive-from'.


rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	Client = seq([
		      ite(p, ndet, assign(p, act, lookup), assign(p, act, alloc)),
		      send(p, e_pid(sv), pair(act, p))
		     ]),
	Server=seq([recv(sv, pair(act, id))]),
	T=(par([Client, Server])),
	Name='simple ite'.


rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	DB=seq([  recv(db, id),
		  send(db, e_var(id), res)
	       ]),
	Client=
	     seq([
		  send(P, e_pid(db), P),
		  recv(P, v)
		 ]),
	     T=(par([for(db, _, s, DB), sym(P, s, while(P, true, Client))])),
	     Rem=sym(P, s, while(P, true, Client)),
	     Name='simple for-while'.

rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	DB=seq([  recv(db, id),
		  send(db, e_var(id), res)
	       ]),
	Client=seq([
		    send(P, e_pid(db), P),
		    recv(P, v)
		   ]),
	T=(par([while(db, true, DB), sym(P, s, Client)])),
	Name='simple_while_in_proc',
	Rem=while(db, true, DB).

/*=========================
        Map-reduce
==========================*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[(q,m)],
	P1A=seq([recv(q, id), send(q, e_var(id), 0)]),
	P1B=seq([recv(q, id), send(q, e_var(id), 1)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([send(P, e_pid(q), P), recv(P, stop),
				if(P, stop=0, send(P, e_pid(m), P))])),
	P3=seq([recv(m, e_pid(s), id)]),
	T=(par([seq([iter(q, k, P1A), for(q, _, s, P1B)]), sym(P, s, P2), iter(m, k, P3)])),
	Name='map-reduce'.

/*========
 Conc DB
==========*/
	
rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	Client = seq([
		      ite(P, ndet, assign(P, act, alloc), assign(P, act, lookup)),
		      send(P, e_pid(db), query, pair(act, P)),
		      ite(P, act=alloc,
			  seq([
			       recv(P, msg),
			       ite(P, msg=free, send(P, e_pid(db), value, acc), skip)
			      ]),
			  recv(P, v))
		     ]),
	Database=seq([
		      recv(db, e_pid(s), query, pair(act, id)),
		      ite(  db, act=alloc,
			    ite(db, ndet,
				seq([
				     send(db, e_var(id), free),
				     recv(db, e_var(id), value, _)
				    ]),
				send(db, e_var(id), allocated)
			       ),
			    send(db, e_var(id), val)
			 )
		     ]),
	T=(par([sym(P, s, Client),  while(db, true, Database)])),
	Rem=while(db, true, Database),
	Name='concdb'.

/*========
 Firewall
==========*/

rewrite_query(T, Rem, Ind, Name) :-
	Ind=[(sv, s)],
	Server=seq([
		    recv(sv,  pair(id, msg)),
		    ite(sv, msg\==bad, send(sv, e_var(id), msg), skip)
		   ]),
	Firewall=seq([
		      recv(fw, e_pid(s), pair(id, msg)),
		      ite(fw,
			  msg=bad,
			  send(fw, e_var(id), wrong_message),
			  seq([
			       send(fw, e_pid(sv), pair(fw, msg)),
			       recv(fw, e_pid(sv), retmsg),
			       send(fw, e_var(id), retmsg)
			      ])
			 )
		     ]),
	Client=seq([send(P, e_pid(fw), pair(P, m)), recv(P, e_pid(fw), ret)]),
	T=( par([
		 while(sv, true, Server),
		 while(fw, true, Firewall),
		 sym(P, s, Client)
		])
	  ),
	Rem=par([while(sv, true, Server), while(fw, true, Firewall)]),
	Name='firewall'.

/*========
 Registry
 ==========*/

rewrite_query(T, skip, [(m,r)], Name) :-
	Master=seq([
		    for(m, P, s, send(m, e_pid(P), r)),
		    recv(m, e_pid(r), _),
		    send(m, e_pid(r), m)
		   ]),
	Registry=seq([
		      for(r, _, s, recv(r, e_pid(s), id)),
		      send(r, e_pid(m), _),
		      recv(r, e_pid(m), id)
		     ]),
	Procs=sym(P, s, seq([
			     recv(P, id),
			     send(P, e_var(id), P)
			    ])
		 ),
	T=par([Master, Registry, Procs]),
	Name='registry'.



/*===========
 Lock-server
 =============*/

 rewrite_query(T, Res, [], Name) :-
	 Client= seq([
		     assign(P, stop, 0),
		     while(P, stop=0,
			   seq([
				send(P, e_pid(sv), lock, P),
				recv(P, e_pid(sv), ack),
				ite(P, ndet,
				    assign(P, act, get),
				    ite(P, ndet,
					assign(P, act, put),
					assign(P, act, unlock)
				       )
				   ),
				send(P, e_pid(sv), action, pair(act,P)),
				ite(P, act=get,
				    recv(P, v),
				    ite(P, act=unlock,
					assign(P, stop, 1),
					skip
				       )
				   )
			       ])
			  )
		    ]),
	 Server=
	 while(sv, true,
	       seq([
		     assign(sv, locked, 0),
		     ite(sv, locked=0,
			 seq([
			      recv(sv, e_pid(s), lock, id),
			      assign(sv, locked, 1),
			      send(sv, e_var(id), ack)
			     ]),
			 skip
			),
		     recv(sv, e_pid(s), action, pair(msg,id)),
		     ite(sv, msg=get,
			 send(sv, e_var(id), v),
			 ite(sv, msg=unlock,
			     assign(sv, lock, 0),
			     skip
			    )
			)
		   ])
	      ),
	 T=par([Server,  sym(P, s, Client)]),
	 Res=Server,
	 Name='lock-server'.