:- use_module(library(avl)).
:- use_module(library(lists)).
:- use_module(library(terms)).
:- use_module(library(ordsets)).
:- use_module('lib/misc.pl', [format_atom/3, fresh_pred_sym/1,
			      substitute_term/4,substitute_term_avl/4,
			      copy_instantiate/4,
			      get_ord_pairs/2]).

:- dynamic independent/2, talkto/2.

/*==============================================================================
 Language:
==============================================================================
 par([A,B,C])     : A || B || C.
 seq([A,B,C])     : A; B; C.
 send(p, x, v)    :
  | x=q           : p sends v to q.
  | x=e_var(y)    : send to the pid stored in variable y.
 recv(p, x)       : p receives x.
 recv(p, x, q)    : p receives x from q.
 sym(P, S, A)     : composition of symmetric processes p in set s with source A.
                    S must be distinct from process ids.
 for(m, P, S, A)  : m executes A for each process p in s.
 skip             : no-operation.
==============================================================================
==============================================================================*/


/*===================================
 TODOs:
===================================
   - while loops
   - receive from
   - for 1..k loops
   - send/receive permissions
===================================
===================================*/

replace_proc_id(Proc1, Proc, Rho, Rho1) :-
	/* Transform all constant assignments for process Proc into mappings for process Proc1 */
	findall(Proc-Var-Val, avl_member(Proc-Var, Rho, Val), L),
	  (   foreach(Proc-Var-Val, L),
	      fromto(Rho, RhoIn, RhoOut, Rho1)
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
	/*     T:    Process term.
	   Gamma:    Environment containing message buffer for each process pair.
	   Delta:    Prefix of rewritten communication.
	     Rho:    Map from variables to constants.
             Psi:    Remainder term given as map from process to list of actions.
	*/
	(
	  /* external send */
	  functor(T, send, 3),
	  arg(1, T, P),
	  arg(2, T, X),
	  atomic(P),
	  functor(X, e_pid, 1),
	  arg(1, X, Q),
	  talkto(P, M),
	  independent(Q, M) ->
	  T1=skip,
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  add_external(Psi, T, P, Psi1)
	/* process remainder term. */
	; functor(T, par, 1),
	  T=par(L),
	  avl_domain(Psi, [P]),
	  \+(talkto(_,_)) ->
	  avl_fetch(P, Psi, [Ext]),
	  append(L, [Ext], L1),
	  T1=par(L1),
	  Gamma1=Gamma,
	  Delta1=Delta,
	  Rho1=Rho,
	  empty_avl(Psi1)	
	/* TODO: external recv-from */
	/* TODO: recv-from */
	  /* recv(p, x) */
	; functor(T, recv, 2),
	  arg(1, T, P),
	  atomic(P),
	  avl_member(Q-P, Gamma, [V|Vs]) ->
	  T1=skip,
	  arg(2, T, X),	  
	  append(Delta, [assign(P, X=V)], Delta1),
	  (   Vs==[] ->
	      avl_delete(Q-P, Gamma, _, Gamma1)
	  ;   avl_store(Q-P, Gamma, Vs, Gamma1)
	  ),
	  avl_store(P-X, Rho, V, Rho1),
	  Psi=Psi1
	/* send(p, x, v)*/
	; functor(T, send, 3) ->
	  arg(1, T, P),
	  arg(2, T, XExp),
	  arg(3, T, V),
	  (   functor(XExp, e_pid, 1) ->
	      arg(1, XExp, Q)
	  ;   functor(XExp, e_var, 1) ->
	      arg(1, XExp, X),
	      avl_fetch(P-X, Rho, Q)
	  ),
	  (   avl_fetch(P-Q, Gamma, Vs)
	  ;   Vs=[]
	  ),
	  append(Vs, [V], Vs1),
	  avl_store(P-Q, Gamma, Vs1, Gamma1),
	  T1=skip,
	  Delta1=Delta,
	  Rho1=Rho,
	  Psi=Psi1
	/* sym(P, S, A): reduce sym(P, S, A) if A does not refer to P. */
	; functor(T, sym, 3),
	  T=sym(P, S, A),
	  \+contains_var(P,A),
	  rewrite(A, Gamma, Delta, Rho, Psi, skip, Gamma, Delta1, Rho1, Psi) ->
	  T1=skip,
	  Gamma1=Gamma,
	  Psi1=Psi
 	  /* par([A,B,C,...]) */
	; functor(T, par, 1) ->
	  arg(1, T, L),
	  (   L==[] ->
	      T1=skip, Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	  /* rewrite single expression */
	  ;   select(A, L, LR),
	      (   A==skip->
		  T1=par(LR), Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	      ;   rewrite_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1) ->
		  T1=par([A1|LR])
	      )
	  /* rewrite ordered pairs of expressions */
	  ;   list_to_ord_set(L, OL),
	      get_ord_pairs(OL, Pairs),
	      select(TL-TR, Pairs, _),
	      rewrite_step(par(TL, TR), Gamma, Delta, Rho, Psi, T2, Gamma1, Delta1, Rho1, Psi1) ->
	      list_to_ord_set([TL,TR], Ts),
	      ord_subtract(OL, Ts, Ts1),
	      T2=par(T2A,T2B),
	      T1=par([T2A,T2B|Ts1])
	  )
	  /* seq([A|B]) */
	; functor(T, seq, 1) ->
	  arg(1, T, L),
	  (   L == [] ->
	      T1=skip, Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	  ;   L=[A|B],
	      (  A==skip ->
		  T1=seq(B),Gamma1=Gamma, Delta1=Delta, Rho1=Rho, Psi=Psi1
	      ;   rewrite_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1) ->
		  T1=seq([A1|B])
	      )
	  )	
	/* par(for(m, P, s, A), sym(Q, s, B)): merge for-loop with parallel composition. */  
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
	  set_talkto(M, Proc),
	  rewrite(par(A1, B1), Gamma, [], Rho2, Psi, par(skip, C), Gamma, Delta2, Rho3, Psi2) ->
	  clear_talkto,
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
	  /* par(A, B): rewrite ordered pairs. */
	; functor(T, par, 2) ->
	  arg(1, T, A),
	  arg(2, T, B),
	  (   rewrite_step(A, Gamma, Delta, Rho, Psi, A1, Gamma1, Delta1, Rho1, Psi1)->
	      T1=par(A1, B)
	  ;   rewrite_step(B, Gamma, Delta, Rho, Psi, B1, Gamma1, Delta1, Rho1, Psi1) ->
	      T1=par(A, B1)
	  ;   functor(A, seq, 1),
	      A=seq([C|Cs]),
	      rewrite_step(par(C, B), Gamma, Delta, Rho, Psi, par(C1, B1), Gamma1, Delta1, Rho1, Psi1)->
	      T1=par(seq([C1|Cs]), B1)
	  )
	).



rewrite(T, Gamma, Delta, Rho, Psi, T2, Gamma2, Delta2, Rho2, Psi2) :-
	(   	T=T2, Gamma=Gamma2, Delta=Delta2, Rho=Rho2, Psi= Psi2
	;   rewrite_step(T, Gamma, Delta, Rho, Psi, T1, Gamma1, Delta1, Rho1, Psi1) ->
	    rewrite(T1, Gamma1, Delta1, Rho1, Psi1, T2, Gamma2, Delta2, Rho2, Psi2)
	;   format('Failed to rewrite term:~p~n' ,[T]), fail
	).

clear_talkto :-
	retractall(talkto(_,_)).

set_talkto(P, Q) :-
	assert(talkto(P,Q)),
	assert(talkto(Q,P)).

init_independent(L) :-
	retractall(independent(_,_)),
	(   foreach((P,Q), L)
	do  assert(independent(P,Q)),
	    assert(independent(Q,P))
	).

rewrite(T, Gamma1, Delta1, Rho1) :-
	empty_avl(Gamma),
	empty_avl(Rho),
	empty_avl(Psi),
	Delta=[],
	rewrite(T, Gamma, Delta, Rho, Psi, skip, Gamma1, Delta1, Rho1, Psi).

pp_term(T, S) :-
	/* TODO */
	(   functor(T, recv, 2) ->
	    arg(1, T, P),
	    arg(2, T, X),
	    format_atom('~p: ~p<-recv()', [P,X], S)
	;   functor(T, send, 3) ->
	    arg(1, T, P),
	    arg(2, T, X)
	).

unit_test :-
	consult([examples]),
	format('===================================================~n',[]),
	format('        Running tests.~n',[]),
	format('===================================================~n',[]),
	findall(T-Name-Ind, rewrite_query(T, Ind, Name), L),
	current_output(Out),
	open_null_stream(Null),
	(   foreach(T-Name-Ind, L),
	    param(Null, Out)
	do (
	     
	     (   init_independent(Ind),
	         set_output(Null),
	         rewrite(T, _, _, _) ->
		 set_output(Out),
		 format('~p:~30|          \e[32mpassed\e[0m~n', [Name])
	     ;   set_output(Out),
		 format('~p:~30|          \e[31mfailed\e[0m~n', [Name])
	     )
	   )
	),
	format('===================================================~n',[]).