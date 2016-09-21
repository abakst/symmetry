:- use_module(library(avl)).
:- use_module(library(lists)).
:- use_module(library(terms)).
:- use_module(library(ordsets)).
:- use_module('lib/misc.pl', [ format_atom/3, fresh_pred_sym/1,
			       substitute_term/4,substitute_term_avl/4,
			       copy_instantiate/4,get_ord_pairs/2,
			       negate/2, bb_inc/1,
			       reset_pred_sym/0
			     ]
	     ).

:- use_module('tags.pl', [check_race_freedom/2]).

:- dynamic independent/2, /* independent(p,q): processes p and q are independent.*/
	talkto/2,     /* talkto(p,q): p and q are communicating, all other procs are external. */
	symset/2.    /* symset(p, S): process p belongs to the set of symmetric processes S. */

/*==============================================================================
 Language:
================================================================================
 par([A,B,C])        : A || B || C.
 seq([A,B,C])        : A; B; C.
 send(p, x, v)       : process p sends value v to
  | x=e_pid(q)       :       - process q.
  | x=e_var(y)       :       - the pid stored in variable y.
send(p, x, type, v)  : send a message of type "type".
 recv(p, v)          : process p receives value v.
 recv(p, x, v)       : process p receives value v from 
  | x=e_pid(q)       :       - process q.
  | x=e_var(y)       :       - the pid stored in variable y.
 recv(p, x, type, v) : receive messages of type "type", only.
 sym(P, S, A)        : composition of symmetric processes p in set s with source A.
                       s must be distinct from process ids.
 for(m, P, S, A)     : process m executes A for each process p in s.
 iter(p, k, A)       : process p executes A k-times.
 while(p, cond, A)   : process p executes A while cond is true.
 nondet(P, A)        : process P is chosen non-deterministically in A.
 assign(p, x, v)     : process p assigns value v to variable x.
 ite(P, Cond, A, B)  : process p executes A if Cond holds and B, otherwise.
 if(P, Cond, A)      : Short for ite(P, Cond, A, skip).
 skip                : no-operation.
 pair(x, y)          : pair of values x and y.

Terms are expected to be of the form par([ seq([..,]), ...]).
==============================================================================
==============================================================================*/

/*===================================
 TODOs:
   - conditionals: variables vs constants.
   - recv(p, q, type, v) as primitive, derive others
   - same for send.
   - Cleanup loop-rules.
   - send/receive permissions.
   - Fix nondet.
   - check rho assignments.
   - Pretty printer.
===================================*/

replace_proc_id(Proc1, Proc, Rho, Rho1) :-
	/* Transform all constant assignments for process Proc into mappings for process Proc1 */
	findall(Proc-Var-Val, avl_member(Proc-Var, Rho, Val), L),
	  (   foreach(Proc-Var-Val, L),
	      fromto(Rho, RhoIn, RhoOut, Rho1),
	      param(Proc1)
	  do  avl_delete(Proc-Var, RhoIn, _, RhoIn1),
	      avl_store(Proc1-Var, RhoIn1, Val, RhoOut)
	  ).

add_external(Psi, T, P, Psi1) :-	
	(  avl_fetch(P, Psi, L)
	;  L=[]
	),
	append(L, [T], L1),
	avl_store(P, Psi, L1, Psi1).
	

rewrite_step(T, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1) :-
	/*
	       T:    Process term.
	   Gamma:    Environment containing message buffer for each process pair.
	   Delta:    Prefix of rewritten communication.
	     Rho:    Map from variables to constants.
             Psi:    Remainder term given as map from process to list of actions.
	*/
	(
	  /*
	  assign(p, x, v): p assigns v to x.
	  */
	  functor(T, assign, 3),
	  T=assign(P, X, V),
	  atomic(P)->
	  T1=skip,
	  append(Delta, [T], Delta1),
	  avl_store(P-X, Rho, V, Rho1),
	  Gamma1=Gamma,
	  Psi1=Psi
	  /*
	  external send/recv-from.
	  */
	; (   functor(T, send, 3)
	  ;   functor(T, recv, 3)
	  ),
	  arg(1, T, P),
	  arg(2, T, X),
	  atomic(P),
	  parse_pid_exp(X, P, Rho, Q),
	  talkto(P, M),
	  independent(Q, M) ->
	  T1=skip,
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  add_external(Psi, T, P, Psi1)
	/*
	Process remainder term.
	Todo: do we need to keep a temporal ordering between
	remainder and later actions of the same process?
	*/
	; functor(T, par, 1),
	  T=par(L),
	  nonvar(Psi),
	  avl_domain(Psi, [P]),
	  \+(talkto(_,_)) ->
	  avl_fetch(P, Psi, Ext),
	  append(L, [seq(Ext)], L1),
	  T1=par(L1),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  empty_avl(Psi1)
	/*
	recv: receive if there's a pending message.
	*/
	; parse_recv(T, Rho, P, Q, Type, X),
	  avl_member(Q-P, Gamma, [V-Type|Vs]) ->
	  T1=skip,
	  append(Delta, [assign(P, X, V)], Delta1),
	  (   Vs==[] ->
	      avl_delete(Q-P, Gamma, _, Gamma1)
	  ;   avl_store(Q-P, Gamma, Vs, Gamma1)
	  ),
	  update_constants(P, X, V, Rho, Rho1),
	  Psi=Psi1
	/*
	send(p, x, v)
	*/
	; (   functor(T, send, 3) ->
	      T= send(P, PidExp, V)
	  ;   functor(T, send, 4) ->
	      T= send(P, PidExp, Type, V)
	  ),
	  parse_pid_exp(PidExp, P, Rho, Q),
	  (   avl_fetch(P-Q, Gamma, Vs)
	  ;   Vs=[]
	  ),
	  substitute_constants(V, P, Rho, V1),
	  append(Vs, [V1-Type], Vs1),
	  avl_store(P-Q, Gamma, Vs1, Gamma1),
	  T1=skip,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi=Psi1
	/*
	sym(P, S, A): reduce A in sym(P, S, A)
	*/
	; functor(T, sym, 3),
	  T=sym(P, S, A),
	  empty_avl(Psi),
	  fresh_pred_sym(Proc),
	  replace_proc_id(Proc, S, Rho, Rho2),
	  copy_instantiate(A, P, Proc, A1),
	  rewrite_step(A1, Gamma, [], Rho2, Psi, B, Gamma, Delta2, Rho3, Psi) ->
	  substitute_term(P, Proc, B, B1),
	  T1=sym(P, S, B1),
	  replace_proc_id(S, Proc, Rho3, Rho1),
	  Gamma1=Gamma,
	  (   Delta2 == [] ->
	      Delta1=Delta
	  ;   substitute_term(P, Proc, Delta2, Delta3),
	      append(Delta, [for(P, S ,Delta3)], Delta1)
	  ),
	  Psi1=Psi
	/*
	sym(P, S, A): reduce sym(P, S, A)
	*/
	; functor(T, sym, 3),
	  T=sym(P, S, A),
	  \+contains_var(P,A),
	  rewrite(A, Gamma, Delta, Rho, Psi, skip, Gamma, Delta1, Rho1, Psi) ->
	  T1=skip,
	  Gamma1=Gamma,
	  Psi1=Psi
	/*
	while(p, cond, A): remove while if cond doesn't hold.
	*/
	; functor(T, while, 3),
	  T= while(P, Cond, _),
	  negate(Cond, NegCond),
	  check_cond(NegCond, P, Rho) ->
	  T1=skip,
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi1=Psi
	/*
	if(P, Cond, A): syntactic sugar for ite(P, Cond, A, skip).
	*/
	; functor(T, if, 3),
	  T=if(P, Cond, A)->
	  T1=ite(P, Cond, A, skip),
	  Gamma1=Gamma, Delta1=Delta,
	  Rho1=Rho, Psi1=Psi
	/*
	ite(P, Cond, A, B): reduce to A, if Cond holds and B, if not Cond holds.
	*/
	; functor(T, ite, 4),
	  T = ite(P, Cond, A, B),
	  (   check_cond(Cond, P, Rho) ->
	      T1=A
	  ;   negate(Cond, NegCond),
	      check_cond(NegCond, P, Rho) ->
	      T1=B
	  )->
	  Gamma1=Gamma, Delta1=Delta,
	  Rho1=Rho, Psi1=Psi
	/*
	par(seq([ite(P, Cond, A, B), C]), D): reduce both par(A,C) and par(B, C) to skip.
	*/
	/*TODO: keep assignments in rho that are occur on both branches.*/
	; functor(T, par, 2),
	  T=par(TA, D),
	  (   functor(TA, seq, 1)->
	      TA=seq([ITE|C]),
	      functor(ITE, ite, 4),
	      ITE=ite(P, Cond, A, B)
	  ;   functor(TA, ite, 4) ->
	      TA=ite(P, Cond, A, B),
	      C=[]
	  ),
	  rewrite(par([seq([A|C]),D]), Gamma, [], Rho, Psi, skip, Gamma, DeltaA, _, Psi),
	  rewrite(par([seq([B|C]),D]), Gamma, [], Rho, Psi, skip, Gamma, DeltaB, _, Psi)->
	  append(Delta, [ite(Cond, seq(DeltaA), seq(DeltaB))], Delta1),
	  empty_avl(Rho1),
	  Gamma1=Gamma,
	  T1=par(skip, skip),
	  Psi1=Psi
	/*
	par([A,B,C,...])
	*/
	; functor(T, par, 1) ->
	  arg(1, T, L),
	  (   L==[] ->
	      T1=skip, Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	  ;   L = [A] ->
	      T1=A, Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	  /*
	  rewrite single expression
	  */
	  ;   select(A, L, LR),
	      (   A==skip->
		  T1=par(LR), Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	      ;   rewrite_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1)->
		  select(A, L, A1, L1),
		  T1=par(L1)
	      )
	  /*
	  rewrite ordered pairs of expressions
	  */
	  ;   list_to_ord_set(L, OL),
	      get_ord_pairs(OL, Pairs),
	      select(TL-TR, Pairs, _),
	      rewrite_step(par(TL, TR), Gamma, Delta, Rho, Psi, T2, Gamma1, Delta1, Rho1, Psi1)->
	      list_to_ord_set([TL,TR], Ts),
	      ord_subtract(OL, Ts, Ts1),
	      T2=par(T2A,T2B),
	      T1=par([T2A,T2B|Ts1])
	  )
	  /*
	  seq([A|B])
	  */
	; functor(T, seq, 1) ->
	  arg(1, T, L),
	  (   L == [] ->
	      T1=skip, Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	  ;   L = [A] ->
	      T1=A, Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	  ;   L=[A|B],
	      (  A==skip ->
		  T1=seq(B),Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	      ;   rewrite_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1)->
		  T1=seq([A1|B])
	      )
	  )
	/*
	nondet(P, A): instantiate P to a fresh constant.
	*/
	; functor(T, nondet, 2) ->
	  T = nondet(P, A),
	  fresh_pred_sym(Proc),
	  (   symset(P, S) ->
	      assert(symset(Proc, S))
	  ;   true
	  ),
	  copy_instantiate(A, P, Proc, T1),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi1=Psi
	/**********************
	        Loops
	**********************/
	/*
	par(iter(p, k, A), iter(q, k, B) ): merge two iter loops.
	*/
	; functor(T, par, 2),
	  arg(1, T, TA),
	  arg(2, T, TB),
	  functor(TA, iter, 3),
	  functor(TB, iter, 3),
	  TA = iter(_, K, A),
	  TB = iter(_, K, B),
	  empty_avl(Psi),
	  mk_pair(A, B, Pair),
	  rewrite(Pair, Gamma, [], Rho, Psi, par(skip, skip), Gamma, Delta2, _, Psi)->
	  T1=par(skip, skip),
	  Gamma1=Gamma, Rho1=Rho, Psi1=Psi,
	  append(Delta, [iter(env, K, seq(Delta2))], Delta1)
	/*
	par(iter(m, k, A), sym(P, s, B)): merge iter-loop with parallel composition.
	*/
	; functor(T, par, 2),
	  arg(1, T, TA),
	  arg(2, T, TB),
	  functor(TA, iter, 3),
	  functor(TB, sym, 3),
	  TA = iter(M, K, A),
	  TB = sym(P, S, B),
	  empty_avl(Psi),
	  fresh_pred_sym(Proc),
	  copy_instantiate(B, P, Proc, B1),
	  replace_proc_id(Proc, S, Rho, Rho2),
	  assert(symset(Proc, S)),
	  set_talkto(M, Proc),
	  mk_pair(A, B1, Pair),
	  rewrite(Pair, Gamma, [], Rho2, Psi, par(skip, B1), Gamma, Delta2, _, Psi2)->
	  clear_talkto,
	  retract(symset(Proc, S)),
	  T1 = par(skip, TB),
	  Gamma1=Gamma,
	  substitute_term(P, Proc, Delta2, Delta3),
	  append(Delta, [iter(env, K , nondet(P, seq(Delta3)))], Delta1),
	  Rho1=Rho,
	  (   avl_delete(Proc, Psi2, Ext0, Psi3) ->
	      substitute_term(Fresh, Proc, Ext0, Ext),
	      add_external(Psi3, iter(S, K, nondet(Fresh, seq(Ext))), S, Psi1),
	      assert(symset(Fresh, S))
	  ;   Psi1=Psi
	  )
	/*
	par(while(m, Cond, A), sym(Q, s, B)): merge for-loop with parallel composition.
	*/
	; functor(T, par, 2),
	  arg(1, T, TA),
	  arg(2, T, TB),
	  functor(TA, while, 3),
	  functor(TB, sym, 3),
	  TA=while(M, Cond, A),
	  TB=sym(P, S, B),
	  empty_avl(Psi),
	  fresh_pred_sym(Proc),
	  check_cond(Cond, M, Rho),
	  replace_proc_id(Proc, S, Rho, Rho2),
	  copy_instantiate(B, P, Proc, B1),
	  set_talkto(M, S),
	  assert(symset(Proc, S)),
	  mk_pair(A, B1, Pair),
	  rewrite(Pair, Gamma, [], Rho2, Psi, par(skip, skip), Gamma, Delta2, Rho3, Psi2)->
	  clear_talkto,
	  retract(symset(Proc, S)),
	  T1=par(TA, skip),
	  replace_proc_id(S, Proc, Rho3, Rho1),
	  Gamma1=Gamma,
	  substitute_term(P, Proc, Delta2, Delta3),
	  append(Delta, [for(P, S , seq(Delta3))], Delta1),
	  (   avl_delete(M, Psi2, Ext, Psi3) ->
	      add_external(Psi3, sym(_, M, seq(Ext)), S, Psi1)
	  ;   Psi1=Psi
	  )
	/*
	par(for(m, P, s, A), sym(Q, s, B)): merge for-loop with parallel composition.
	*/
	; functor(T, par, 2),
	  arg(1, T, TA),
	  arg(2, T, TB),
	  functor(TA, for, 4),
	  functor(TB, sym, 3), 
	  TA=for(M, P, S, A),
	  TB=sym(Q, S, B),
	  empty_avl(Psi),
	  fresh_pred_sym(Proc),
	  replace_proc_id(Proc, S, Rho, Rho2),
	  copy_instantiate(A, P, Proc, A1),
	  copy_instantiate(B, Q, Proc, B1),
          assert(symset(Proc, S)),
	  set_talkto(M, Proc),
          mk_pair(A1, B1, Pair),
	  rewrite(Pair, Gamma, [], Rho2, Psi, par(skip, C), Gamma, Delta2, Rho3, Psi2) ->
	  clear_talkto,
          retract(symset(Proc, S)),
	  substitute_term(Q, Proc, C, C1),
	  T1=par(skip, sym(Q, S, C1)),
	  replace_proc_id(S, Proc, Rho3, Rho1),
	  Gamma1=Gamma,
	  substitute_term(P, Proc, Delta2, Delta3),
	  append(Delta, [for(P, S ,Delta3)], Delta1),
	  % External
	  % TODO: keep remainder for for-loop process.
	  (   avl_delete(Proc, Psi2, Ext0, Psi3) ->
	      substitute_term(P, Proc, Ext0, Ext),
	      add_external(Psi3, sym(P, S, seq(Ext)), S, Psi1)
	  ;   Psi1=Psi
	  )
	/*
	par(A, while(P, Cond, B)): consume A.
	*/
	; functor(T, par, 2),
	  arg(1, T, A),
	  arg(2, T, TB),
	  functor(TB, while, 3),
	  TB=while(P, Cond, B),
	  check_cond(Cond, P, Rho),
	  empty_avl(Psi),
          mk_pair(A, B, Pair),
	  rewrite(Pair, Gamma, [], Rho, Psi, par(skip, skip), Gamma, Delta2, Rho1, Psi1) ->
	  T1=par(skip, TB),
	  append(Delta, [Delta2], Delta1),
	  Gamma1=Gamma
	  /*
	  par(A, B): rewrite ordered pairs.
	  */
	; functor(T, par, 2) ->
	  arg(1, T, A),
	  arg(2, T, B),
	  (   rewrite_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1)->
	      T1=par(A1, B)
	  ;   rewrite_step(B, Gamma, Delta, Rho, Psi, B1, Gamma1, Delta1, Rho1, Psi1)->
	      T1=par(A, B1)
	  ;   functor(A, seq, 1),
	      A=seq([C|Cs]),
	      rewrite_step(par(C, B), Gamma, Delta, Rho, Psi, par(C1, B1), Gamma1, Delta1, Rho1, Psi1)->
	      T1=par(seq([C1|Cs]), B1)
	  )
	).

rewrite(T, Gamma, Delta, Rho, Psi, T2, Gamma2, Delta2, Rho2, Psi2) :-
	(   match(T, T2),
	    %T=T2,
	    Gamma=Gamma2, Delta=Delta2, Rho=Rho2, Psi= Psi2
	;   rewrite_step(T, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1) ->
	    sanity_check([T1, Gamma1, Delta1, Rho1, Psi1]),
	    rewrite(T1, Gamma1, Delta1, Rho1, Psi1, T2, Gamma2, Delta2, Rho2, Psi2)
	;   format('Failed to rewrite term:~p~n' ,[T]), fail
	).

match(T, T1) :-
	/*
	Try to match T and T1 by permuting the elements of L in par(L).
	*/
	(   T=T1 ->
	    true
	;   functor(T, par, 1),
	    functor(T1, par, 1),
	    T=par(L),
	    T1=par(L1),
	    permutation(L, L1)
	).


mk_pair(A, B, Pair) :-
	(   Pair=par(A, B)
	;   Pair=par(B, A)
	).

sanity_check(L) :-
	(   foreach(X, L)
	do  nonvar(X)->
	    true
	;   throw(parameter_not_instantiated(X))
	).

parse_recv(T, Rho, P, Q, Type, V) :-
/*
recv(p, q, type, v): p receives a message v of type "type" from process q.
*/
	(   (   functor(T, recv, 2)->
		T=recv(P, V)
	    ;	functor(T, recv, 3)->
		T=recv(P, PidExp, V)
	    ;   functor(T, recv, 4) ->
		T=recv(P, PidExp, Type, V)
	    ),
	    atomic(P),
	    (   nonvar(PidExp) ->
		parse_pid_exp(PidExp, P, Rho, Q0),
		(   symset(Q, Q0)
		;   Q=Q0
		)
	    ;   true
	    )
	).

parse_pid_exp(PidExp, P, Rho, Q) :-
	/*
	If PidExp is of the form e_pid(q), return q.
	If PidExp is of the form e_var(x) return rho(p, x).
        Throws an exception otherwise.
	*/
	(   functor(PidExp, e_pid, 1) ->
	    arg(1, PidExp, Q)
	;   functor(PidExp, e_var, 1) ->
	    arg(1, PidExp, X),
	    avl_fetch(P-X, Rho, Q)
	;   throw(parse-pid-error(PidExp))
	).

update_constants(P, X, V, Rho, Rho1) :-
	(   atomic(V) ->
	    avl_store(P-X, Rho, V, Rho1)
	;   var(V) ->
	    Rho1=Rho
	;   functor(X, pair, 2),
	    functor(V, pair, 2),
	    X=pair(X1, X2),
	    V=pair(V1, V2) ->
	    update_constants(P, X1, V1, Rho, Rho2),
	    update_constants(P, X2, V2, Rho2, Rho1)
	;   throw(pair-matching-error(X,V))
	).

substitute_constants(T, P, Rho, T1) :-
	/*
	In term T substitute all variable bindings defined in Rho to
	produce term T1.
	*/
	avl_domain(Rho, Dom),
	(   foreach(Q-Var, Dom),
		fromto(T, In, Out, T1),
		param(Rho, P)
	    do  (  Q==P ->
		    avl_fetch(P-Var, Rho, Val),
		    substitute_term(Val, Var, In, Out)
		;   In=Out
		)
	).

check_cond(Cond, P, Rho) :-
	/*
	Check whether condition Cond holds under
	variable assignment Rho.
	*/
	(   Cond==true ->
	    true
	;   substitute_constants(Cond, P, Rho, Cond1),
	    catch(Cond1, _, fail)
	).

clear_talkto :-
	retractall(talkto(_,_)).

set_talkto(P, Q) :-
	assert(talkto(P,Q)),
	assert(talkto(Q,P)).

init_independent(L) :-
	/*
	L=[(m,n),..] : processes m and n
	are independent.
	*/
	(   foreach((P,Q), L)
	do  assert(independent(P,Q)),
	    assert(independent(Q,P))
	).

cleanup :-
	clear_talkto,
	retractall(independent(_,_)),
	retractall(talkto(_,_)),
	retractall(symset(_,_)),
	reset_pred_sym.

rewrite(T, Rem, Ind, Gamma1, seq(Delta1), Rho1) :-
	init_independent(Ind),
	empty_avl(Gamma),
	empty_avl(Rho),
	empty_avl(Psi),
	Delta=[],
	rewrite(T, Gamma, Delta, Rho, Psi, Rem, Gamma1, Delta1, Rho1, Psi).

format_result(Goal, Res) :-
	(   Goal->
	    Res='\e[32mpassed\e[0m'
	;   Res='\e[31mfailed\e[0m'
	).

unit_test :-
	consult([examples]),
	format('================================================================~n',[]),
	format('~p:~30|~p~t~10+~p~t~13+~p~t~70|~n', ['Name','rewrite','race-check','time']),
	format('================================================================~n',[]),
	findall(T-Rem-Name-Ind, rewrite_query(T, Rem, Ind, Name), L),
	current_output(Out),
	open_null_stream(Null),
	(   foreach(T-Rem-Name-Ind, L),
	    param(Null, Out)
	do (
	     set_output(Null),
	     cleanup,
	     statistics(runtime, [T0|_]),
	     format_result(catch(check_race_freedom(T, _), _, fail), Race),
	     format_result(rewrite(T, Rem, Ind, _, _, _), Rewrite),
	     statistics(runtime, [T1|_]),
	     Time is (T1-T0),
	     set_output(Out),
	     format('~p:~t~30|~p~t~21+~p~t~18+~t~d~3+~t ms~50|~n', [Name,Rewrite,Race,Time])
	   )
	),
	format('================================================================~n',[]).