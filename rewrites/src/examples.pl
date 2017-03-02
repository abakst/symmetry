
/*===========================================
Examples specified as queries of the form

   rewrite_query(T, Rem, Ind, Name).

- T    : Term to be rewritten
- Rem  : Expected remainder term.
- Ind  : List of pairs of independent processes.
- Name : Example name.
===========================================*/

/*==============
 Unfolding:
================*/


/*===========
Unfold-send
===========*/

rewrite_query(T, Rem, Ind, Name) :-
	T=par([
	       seq([
		    assume(element(p, s)),
		    send(m, e_pid(p), v)
		   ]),
	       sym(P, s,
		   recv(P, v)
		  )
	      ]),
	Rem=sym(P, set_minus(s, p), recv(P, v)),
	Name=unfold-send.

/*===========
Unfold-recv
===========*/

rewrite_query(T, Rem, Ind, Name) :-
	T=par([
	       seq([
		    assume(prop_subset(emp, s1)),
		    assume(subset(s1, s)),
		    recv(m, e_pid(s), v)
		   ]),
	       sym(P, s1,
		   send(P, e_pid(m), v)
		  )
	      ]),
	Rem=sym(P, set_minus(s1, Q), send(P, e_pid(m), v)),
	Name=unfold-recv.

/*==============
while-loop-once:
================*/
rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	P1=seq([
		recv(m, id),
		send(m, e_var(id), m)
		]),
	P2=while(P, true,
		 seq([
		      send(P, e_pid(m), P),
		      recv(P, v)
		     ])
		),
	T= par([P1, sym(P, s, P2)]),
	Rem=sym(P, s, P2),
	Name=while-sym-once.



/*===========
 For-loop
===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=seq([recv(m, e_pid(s), id)]),
	P2=seq([send(P, e_pid(m), P)]),
	T=(par([for(m, _, s, P1), sym(P, s, P2)])),
	Name=unfold-for-simple.


rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=seq([recv(m, e_pid(s), id), send(m, e_var(id), m)]),
	P2=seq([send(P,e_pid(m), P), recv(P, x)]),
	T=(par([for(m, _, s, P1), sym(P, s, P2)])),
	Name=unfold-for.

/*===========
 sym-while
===========*/

rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	DB=seq([  recv(db, e_pid(s), id),
		  send(db, e_var(id), res)
	       ]),
	Client=seq([
		    send(P, e_pid(db), P),
		    recv(P, v)
		   ]),
	T=(par([sym(P, s, Client),while(db, true, DB)])),
	Name='simple_while_in_proc',
	Rem=while(db, true, DB).

/*==============
Iter-loop:
================*/
rewrite_query(T, Rem, Ind, Name) :-
	P1=seq([
		recv(m, e_pid(s), id),
		send(m, e_var(id), m)
		]),
	P2=while(P, true,
		 seq([
		      send(P, e_pid(m), P),
		      recv(P, e_pid(m), v)
		     ])
		),
	T= par([iter(m, k, P1), sym(P, s, P2)]),
	Rem=sym(P, s, P2),
	Name=iter-while-simple.


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
	P1=seq([send(m, e_pid(Q), m), recv(m, e_pid(Q), x)]),
	P2=seq([recv(P, e_pid(m), id), send(P,e_pid(m),P)]),
	T=(par([for(m, Q, s, P1), sym(P, s, P2)])),
	Name=simple-ping-loop.

/*===========
Reverse ping
===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1=seq([recv(m, e_pid(s), id), send(m,e_var(id), m)]),
	P2=seq([send(P,e_pid(m),P), recv(P, x)]),
	T=(par([for(m, _, s, P1), sym(P, s, P2)])),
	Name=reverse-ping.

/*===========
 Two loops
===========*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1=seq([send(m, e_pid(Q), m)]),
	P2=seq([recv(P, id)]),
	T=(par([seq([for(m, Q, s, P1)]), sym(P, s, P2)])),
	Name=two-loops-simple.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1A=seq([send(m, e_pid(Q), m)]),
	P1B=seq([recv(m, e_pid(s), x)]),
	P2=seq([recv(P, id), send(P, e_pid(m), P)]),
	T=(par([seq([for(m, Q, s, P1A), for(m, Q, s, P1B)]), sym(P, s, P2)])),
	Name=two-loops.

/*============
Two loops var
===============*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1A=seq([send(m,e_pid(Q), m)]),
	P1B=seq([recv(m, e_pid(s), x)]),
	P2=seq([recv(P, id), send(P,e_var(id),P)]),
	T=(par([for(m, Q, s, P1A), for(m, Q, s, P1B), sym(P, s, P2)])),
	Name=two-loops-var.

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
	P1=seq([recv(q, e_pid(s), id), send(q, e_var(id), 1)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([send(P, e_pid(q), P), recv(P, e_pid(q), stop)])),
	T=(par([for(q, _, s, P1), sym(P, s, P2)])),
	Name=work-stealing2.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1A=seq([recv(q, e_pid(s), id), send(q, e_var(id), 0)]),
	P1B=seq([recv(q, e_pid(s), id), send(q, e_var(id), 1)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([send(P, e_pid(q), P), recv(P, stop)])),
	T=(par([seq([iter(q, k, P1A), for(q, _, s, P1B)]), sym(P, s, P2)])),
	Name=work-stealing.

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
	 P3=seq([recv(n, e_pid(s), x)]),
	 T=(par([for(m, Q, s, P1), sym(P, s, P2), for(m, _, s, P3)])),
	Name='two-party ping'.

/*=========================
Interleaved two-party ping
==========================*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[(m,n)],
	P1=seq([recv(m, e_pid(s), id), send(m, e_var(id), m)]),
	P2=seq([send(P, e_pid(m), P), send(P, e_pid(n), P), recv(P, e_pid(m), id)]),
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



/*=========================
        Map-reduce
==========================*/

rewrite_query(T, Rem, Ind, Name) :-
	Ind=[(q,m)],
	P1A=seq([recv(q, e_pid(s), id), send(q, e_var(id), 0)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([
				send(P, e_pid(q), P), recv(P, stop),
				if(P, stop=0, send(P, e_pid(m), P))
			       ])),
	P3=seq([recv(m, e_pid(s), id)]),
	T=(par([seq([iter(q, k, P1A)]), sym(P, s, P2), iter(m, k, P3)])),
	Rem=sym(P,s, W),
	Name=map-reduce-simple.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[(q,m)],
	P1A=seq([recv(q, e_pid(s), id), send(q, e_var(id), 0)]),
	P1B=seq([recv(q, e_pid(s), id), send(q, e_var(id), 1)]),
	P2=seq([assign(P, stop, 0), W]),
	W=while(P, stop=0, seq([send(P, e_pid(q), P), recv(P, stop),
				if(P, stop=0, send(P, e_pid(m), P))])),
	P3=seq([recv(m, e_pid(s), id)]),
	T=(par([seq([iter(q, k, P1A), for(q, _, s, P1B)]), sym(P, s, P2), iter(m, k, P3)])),
	Name=map-reduce.

/*========
 Conc DB
==========*/


rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	Client = seq([
		      ite(P, ndet, assign(P, act, alloc), assign(P, act, lookup)),
		      send(P, e_pid(db), query, pair(act, P))
		     ]),
	Database=seq([
		      recv(db, e_pid(s), query, pair(act, id))
		     ]),
	T=(par([while(db, true, Database), sym(P, s, Client)])),
	Rem=while(db, true, Database),
	Name='simple-concdb'.



rewrite_query(T, skip, Ind, Name) :-
	P=p,
	Client=seq([
		    recv(P, msg),
		    ite(P, msg==free, send(P, e_pid(db), value, acc), skip)
		   ]),
	Server=ite(db, ndet,seq([
			  send(db, e_pid(p), free),
			  recv(db, e_pid(p), value, _)
				]),
		  send(db, e_pid(p), allocated)
		  ),
	Name=db-ite,
	T=par([Client,Server]).

	
rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	P=p,
	Client = seq([
		      assign(P, act, alloc),
		      send(P, e_pid(db), query, pair(act, P)),
		      ite(P, act=alloc,
			  seq([
			       recv(P, msg),
			       ite(P, msg==free, send(P, e_pid(db), value, acc), skip)
			      ]),
			  recv(P, v))
		     ]),
	Database=seq([
		      recv(db, e_pid(p), query, pair(act, id)),
		      ite(  db, act==alloc,
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
	T=(par([Database,  Client])),
	Rem=skip,
	Name='concdb-seq'.

rewrite_query(T, Rem, Ind, Name) :-
	Ind=[],
	Client = seq([
		      ite(P, ndet, assign(P, act, alloc), assign(P, act, lookup)),
		      send(P, e_pid(db), query, pair(act, P)),
		      ite(P, act==alloc,
			  seq([
			       recv(P, msg),
			       ite(P, msg==free, send(P, e_pid(db), value, acc), skip)
			      ]),
			  recv(P, v))
		     ]),
	Database=seq([
		      recv(db, e_pid(s), query, pair(act, id)),
		      ite(  db, act==alloc,
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
	T=(par([while(db, true, Database), sym(P, s, Client)])),
	Rem=while(db, true, Database),
	Name='concdb'.

/*========
 Firewall
==========*/

rewrite_query(T, Rem, Ind, Name) :-
	Ind=[(sv, s)],
	Server=seq([
		    recv(sv, pair(id, msg)),
		    ite(sv, msg\==bad, send(sv, e_var(id), msg), skip)
		   ]),
	Firewall=seq([
		      recv(fw, e_pid(s), pair(id, msg)),
		      ite(fw,
			  msg==bad,
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
		      send(P, e_pid(sv), lock, P),
		      recv(P, e_pid(sv), ack),
		      iter(P, k,
			   send(P, e_pid(sv), action, pair(act,P))
			  )
		      /*
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
				ite(P, act==get,
				    recv(P, v),
				    ite(P, act=unlock,
					assign(P, stop, 1),
					skip
				       )
				   )
			       ])
			  )
		      */
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
		     recv(sv, e_var(id), action, pair(msg,id)),
		     ite(sv, msg==get,
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

/*============
Error handling
===============*/

rewrite_query(T, skip, Ind, Name) :-
	Ind=[], 
	P1A=seq([send(m,e_pid(Q), m)]),
	P1B=seq([recv(m, e_pid(s), x)]),
	P2=seq([recv(P, id), send(P,e_var(ip),P)]),
	T=(par([for(m, Q, s, P1A), for(m, Q, s, P1B), sym(P, s, P2)])),
	Name=error-simple.

/*================
Cases statements
==================*/

rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        %%%%% proctype A:
        TA=seq([
		recv(A, type(ping), val),
                cases(A, val,
                       [ case(A, ping(Q),
                              seq([
				   send(A, e_pid(Q), pong, A)
				  ])
			     )
                       ],
		      default(A, die(A))
		     )
               ]),
        %%%%% proctype B:
        TB=seq([ send(B, e_pid(A), ping, ping(B)), recv(B, type(pong), var)]),
        %%%%%
        T=par([TA,TB]),
	A=a, B=b,
        Name=cases-minimal.


rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        %%%%% proctype A:
        TA=seq([ recv(A, type(tyCon(ty__Ping)), ds_ddfZ),
                 cases(A, ds_ddfZ,
                       [ case(A, cstr__Ping(Q),
                              send(A, e_pid(Q), tyCon(ty__ProcessId), A)
			     )
			     ],		     
                       _)
               ]),
        %%%%% proctype B:
        TB=seq([ assign(B, anf0, cstr__Ping(B)),
                 send(B, e_pid(A), tyCon(ty__Ping), anf0),
                 recv(B, type(tyCon(ty__ProcessId)), q)
               ]),
        %%%%%
	A=a, B=b,
        T=par([TA,TB]),
        Name=simple-cases-parts.



rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        %%%%% proctype A:
        TA=seq([ recv(A, type(tyCon(ty__Ping)), ds_ddfZ),
                 cases(A, ds_ddfZ,
                       [ case(A, cstr__Ping(Q),
                              seq([ send(A, e_pid(Q), tyCon(ty__ProcessId),  A),
                                    recv(A, type(tyCon(ty__ABigRecord)), msg), 
				    cases(A, msg, [case(A, cstr__Foo(_, Ds_ddg7), assign(A, anf0, Ds_ddg7))], _),
				    assign(A, anf1, cstr__Unit),
                                    send(A, e_var(anf0), tyCon(ty__Tuple), anf1)]))
                       ],
				  default(A, die(A))
				 )
               ]),
        %%%%% proctype B:
        TB=seq([
		assign(B, anf0, cstr__Ping(B)),
		send(B, e_pid(A), tyCon(ty__Ping), anf0),
		recv(B, type(tyCon(ty__ProcessId)), q),
		assign(B, anf1, cstr__Foo(0, B)),
		send(B, e_var(q), tyCon(ty__ABigRecord), anf1),
		recv(B, type(tyCon(ty__Tuple)), q)
               ]),
	A=a, B=b,
        %%%%%
        T=par([TA,TB]),
        Name=simple-cases.

rewrite_query(T, skip, [], Name) :-
	T=par([
	       seq([
		    assign(A, anf0, cstr__SelfSigned(e_pid(A), e_pid(A))),
		    send(A, e_pid(B), tyCon(ty__SelfSigned, tyCon(ty__ProcessId)), anf0) 
		   ]),
	       seq([
		    recv(B, e_pid(A), tyCon(ty__SelfSigned, tyCon(ty__ProcessId)), msg) 
		   ])
	      ]),
	A=a,
	B=b,
	Name=de-casify-simple.





rewrite_query(T, skip, [], Name) :-
	T=par([
	       seq([
		    assign(A, anf0, cstr__SelfSigned(e_pid(A), A)),
		    send(A, e_pid(B), tyCon(ty__SelfSigned, tyCon(ty__ProcessId)), anf0),
		    recv(A, e_pid(B), tyCon(ty__SelfSigned, tyCon(ty__Int)), msg)

		   ]),
	       seq([
		    recv(B, e_pid(A), tyCon(ty__SelfSigned, tyCon(ty__ProcessId)), msg),	%,
		   
		    cases(B, msg, [
				   case(B, cstr__SelfSigned(X, Pay), assign(B, who, Pay))
				  ],
			  _),
		    ite(B, ndet, assign(B, anf1, 1), assign(B, anf1, 0)),
/*
		    cases(B, ndet, [
				    case(B, cstr__False, assign(B, anf1, 1)),
				    case(B, cstr__True, assign(B, anf1, 0))
				   ],
			  _),
*/		    
		    assign(B, blub, cstr__SelfSigned(e_pid(B), anf1)),
		    send(B, e_var(who), tyCon(ty__SelfSigned, tyCon(ty__Int)), blub)
		   
		   ])
	      ]),
	A=a,
	B=b,
	Name='de-casify'.




rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        %%%%% proctype A:
        TA=seq([
                cases(A, act,
		      [ case(A, ping(Q),
			     send(A, e_pid(Q), pong, act)
			    ),
			case(A, pong(Q),
			     send(A, e_pid(Q), pong, act)
			    )
		      ],
		      skip)
               ]),
        %%%%% proctype B:
        TB=seq([ recv(B, var)]),
        %%%%%
        T=par([TA,TB]),
	A=a, B=b,
        Name=cases-simple-choice.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1A=seq([send(m, e_pid(Q), m)]),
	P1B=seq([recv(m, e_pid(s), x)]),
	P2= seq([
		 assign(P, act, ping(m)),
		 cases(P, act,
		       [ case(P, ping(X),
			      seq([recv(P, id), send(P, e_pid(X), P)])
			     )
		       ], skip)
		]),
	T=(par([seq([for(m, Q, s, P1A), for(m, Q, s, P1B)]), sym(P, s, P2)])),
        Name=cases-split-loop.


rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=seq([
		 send(m, e_pid(Q), m),
		 recv(m, e_pid(Q), x),
		 cases(m, x,
		       [
			case(m, ping(Proc), skip),
			case(m, pong(Proc), skip)
		       ],
		       skip)
		]),
	P2= seq([
		 recv(P, id),
		 cases(P, val,
		       [
			case(P, ping(P), skip),
			case(P, pong(P), skip)
		       ],
		       skip),
		 send(P, e_var(id), val)
		]),
	T=(par([seq([for(m, Q, s, P1)]), sym(P, s, P2)])),
        Name=case-cond-branch-loop.

rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1=seq([
		 send(m, e_pid(P), m),
		 recv(m, e_pid(P), x),
		 cases(m, x,
		       [
			case(m, ping(M), skip),
			case(m, pong(M), skip)
		       ],
		       skip)
		]),
	P2= seq([
		 cases(P, val,
		       [
			case(P, ping(P), skip),
			case(P, pong(P), skip)
		       ],
		       skip),
		 recv(P, id),
		 send(P, e_var(id), val)
		]),
	T=(par([P1, P2])),
	P=p,
        Name=case-cond-branch.

rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        T=par([TA,TB]),
        TA=seq([
		assign(A, ds_ddbB, cstr__Unit),
		for(A, _, set(B_Set),
		    seq([
			 recv(A, type(tyCon(ty__Lock)), ds_ddbG),
			 cases(A, ds_ddbG, [ case(A, cstr__Lock(P),
						  seq([
						      send(A, e_pid(P), tyCon(ty__Grant), cstr__Granted),
						      recv(A, e_pid(P), tyCon(ty__SelfSigned, tyCon(ty__Release)), msg),

						       cases(A, msg, [
								      case(A, cstr__SelfSigned(_, Pay), assign(A, ds_ddbD, Pay))
								     ],
							     skip),
						       cases(A, ds_ddbD, [
									  case(A, cstr__Release, assign(A, ds_ddbB, cstr__Unit))
									 ], skip)
						      ])
						 )
					   ], skip)
			])
		   )
	       ]),
	
        TB=sym(B, set(B_Set), seq([
				   assign(B, anf0, cstr__Lock(B)),
				   send(B, e_pid(A), tyCon(ty__Lock), anf0),
				   recv(B, type(tyCon(ty__Grant)), ds_ddbR),
				   assign(B, ds_ddbR, cstr__Granted),
				   cases(B, ds_ddbR, [
						      case(B, cstr__Granted,
							   seq([
								assign(B, anf1, cstr__SelfSigned(B, cstr__Release)),
								send(B, e_pid(A), tyCon(ty__SelfSigned, tyCon(ty__Release)), anf1)
							       ])
							  )
						     ], skip)
				  ])

	      ),
        A=a,
        B_Set=bs,
        Name=lock-server.


rewrite_query(T, skip, Ind, Name) :-
	Ind=[],
	P1A=seq([ send(m, e_pid(Q), m) ]),
	P1B=seq([
		 recv(m, e_pid(s), x),
		 cases(m, x,
		       [
			case(m, ping(Proc), skip),
			case(m, pong(Proc), skip)
		       ],
		       skip)
		]),
	P2= seq([
		 recv(P, id),
		 cases(P, val,
		       [
			case(P, ping(P), skip),
			case(P, pong(P), skip)
		       ],
		       skip),
		 send(P, e_var(id), val)
		]),
	T=(par([seq([for(m, Q, s, P1A), for(m, Q, s, P1B)]), sym(P, s, P2)])),
        Name=cases-split-loop2.



rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        %%%%% proctype A:
        TA=seq([
		for(A, _, set(B_Set), seq([
					   recv(A, type(tyCon(ty__AcceptorResponse)), msg) %,
				      ])

		   ),
%		assign(A, ds_dbw4, cstr__Unit),
		for(A, X, set(B_Set),
%		    cases(A, ds_dbw4, [
%				       case(A, cstr__Unit, seq([ assign(A, anf1, cstr__Rollback(A)),
								 send(A, e_pid(X), tyCon(ty__CoordMessage), anf1) %]) )
%				      ],skip)
		   )

	       ]),
        TB=  sym(B, set(B_Set),
		 seq([
		      assign(B, ds_dbwi, cstr__Tuple(a, fn)),
		      cases(B, ds_dbwi,
			    [
			     case(B, cstr__Tuple(Who, Fn), seq([
								/*
								cases(B, ndet, [
										case(B, cstr__False,
										     assign(B, anf0, cstr__Reject)),
										case(B, cstr__True,
										     assign(B, anf0, cstr__Accept(B)))
									       ], skip
								     ),
								*/
								send(B, e_pid(a), tyCon(ty__AcceptorResponse), anf0),
								recv(B, type(tyCon(ty__CoordMessage)), msg)			
							       ])
				 )
			    ], skip)
		     ])
		),
        T=par([TA,TB]),
        A=a,
        B_Set=bs,
        Ind=[],
        Name=2-phase-commit-debug.

rewrite_query(T,skip,Ind,Name) :-
        Ind=[],
        %%%%% proctype A:
        TA=seq([
		assign(A, ds_dbw6, cstr__Unit),
		 for(A, X, set(B_Set),
		     cases(A, ds_dbw6, [
					case(A, cstr__Unit,
					     seq([
						  assign(A, anf0, cstr__Tuple(A, fn)),
						  send(A, e_pid(X), tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__String)), anf0)
						 ])
					    )
				       ], skip)
		    ),
	        assign(A, x, 0),
		for(A, _, set(B_Set), seq([
					   recv(A, type(tyCon(ty__AcceptorResponse)), msg),
					    cases(A, msg, [
							   case(A, cstr__Accept(Ds_dbwf), assign(A, x, ndet1)),
							   case(A, cstr__Reject, skip)
							  ], skip
						 )
				      ])

		   ),

		(
		  cases(A, ndet2, [
				 case(A, cstr__False, seq([
							   assign(A, ds_dbw4, cstr__Unit),
							   for(A, X, set(B_Set),
							       cases(A, ds_dbw4, [
										  case(A, cstr__Unit, seq([ assign(A, anf1, cstr__Rollback(A)),
													    send(A, e_pid(X), tyCon(ty__CoordMessage), anf1)]))
										 ],skip)
							      )
							  ])
				     ),
				 case(A, cstr__True, seq([
							  assign(A, ds_dbw2, cstr__Unit),
							  for(A, X, set(B_Set),
							      cases(A, ds_dbw2, [ case(A, cstr__Unit,
										       seq([ assign(A, anf2, cstr__Commit(A)),
											     send(A, e_pid(X), tyCon(ty__CoordMessage), anf2)]))
										], skip)
							     )
							 ])
				     )
				  ], skip)
		)
		]),
	       TB=sym(B, set(B_Set),
		      seq([
			   recv(B, type(tyCon(ty__Tuple, tyCon(ty__ProcessId), tyCon(ty__String))), ds_dbwi),
			   cases(B, ds_dbwi,
				 [
				  case(B, cstr__Tuple(Who, Fn), seq([
								     
								     cases(B, ndet, [
										     case(B, cstr__False,
											  assign(B, anf0, cstr__Reject)),
										     case(B, cstr__True,
											  assign(B, anf0, cstr__Accept(B)))
										    ], skip
									  ),
								     send(B, e_pid(a), tyCon(ty__AcceptorResponse), anf0),
								     recv(B, type(tyCon(ty__CoordMessage)), msg),
								     cases(B, msg, [
										    case(B, cstr__Commit(P), assign(B, anf1, P)),
										    case(B, cstr__Rollback(P), assign(B, anf1, P))
										   ], skip
									  )%,
%								     send(B, e_var(anf1), tyCon(ty__AcceptorAck), cstr__ACK)
								    ])
				      )
			    ], skip)
		     ])
		),
        T=par([TA,TB]),
        A=a,
        B_Set=bs,
        Ind=[],
        Name=2-phase-commit.


