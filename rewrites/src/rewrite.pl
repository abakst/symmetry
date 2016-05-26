:- use_module(library(avl)).
:- use_module(library(terms)).
:- use_module(library(ordsets)).
:- use_module('lib/misc.pl', [format_atom/3, fresh_pred_sym/1, substitute_term/4,copy_instantiate/4]).

%% par(A,B)     : A || B .
%% seq([A,B,C]) : A;B;C .
%% send(p, x, v): p sends v to q.
%%  | x=e_pid(q): send to  pid p.
%%  | x=e_var(y): send to the pid stored in variable y.
%% recv(p, x)   : p receives x.
%% sym(P, S, A)    : composition of symmetric processes p in set s with source A.
%% for(P, S, A)    : for each process p in s execute A.
%% skip         : no-operation.



rewrite_step(T, Gamma, Delta, Rho, T1, Gamma1, Delta1, Rho1) :-
	(
	  %recv(p, x)
	  functor(T, recv, 2),
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
	  avl_store(P-X, Rho, V, Rho1)
	;
	  %send(p, x, v)
	  functor(T, send, 3) ->
	  arg(1, T, PExp),
	  arg(2, T, XExp),
	  arg(3, T, V),
	  functor(PExp, e_pid, 1),
	  arg(1, PExp, P),
	  (   functor(XExp, e_pid, 1) ->
	      arg(1, XExp, Q)
	  ;   functor(XExp, e_var, 1) ->
	      arg(1, XExp, X),
	      avl_fetch(P-X, Rho, Q),
	      format("Q: ~p",[Q])
	  ),
	  (   avl_fetch(P-Q, Gamma, Vs)
	  ;   Vs=[]
	  ),
	  append(Vs, [V], Vs1),
	  avl_store(P-Q, Gamma, Vs1, Gamma1),
	  T1=skip,
	  Delta1=Delta,
	  Rho1=Rho
	%TODO check for all pairs.
	%par(for(P,s,A), sym(Q,s,B))
	; functor(T, par, 2),
	  arg(1, T, TA),
	  arg(2, T, TB),
	  functor(TA, for, 3),
	  functor(TB, sym, 3), 
	  TA=for(P,S,A),
	  TB=sym(Q,S,B),
	  fresh_pred_sym(Proc),
	  copy_instantiate(A, P, Proc, A1),
	  copy_instantiate(B, Q, Proc, B1),
	  rewrite(par(A1,B1), Gamma, [], Rho, par(skip, C), Gamma, Delta2, _) ->
	  substitute_term(Q, Proc, C, C1),
	  T1=C1,
	  Rho1=Rho, %TODO: safe constants from loop
	  Gamma1=Gamma,
	  substitute_term(P, Proc, Delta2, Delta3),
	  append(Delta, for(P,Delta3), Delta1)

	%Todo: par([A,B,C,...]).
	%par(A, B)
	; functor(T, par, 2) ->
	  arg(1, T, A),
	  arg(2, T, B),
	  (   A==skip, B==skip ->
	      T1=skip, Gamma1=Gamma, Delta1=Delta, Rho1=Rho
	  ;   rewrite_step(A, Gamma, Delta, Rho, A1, Gamma1, Delta1, Rho1)->
	      T1=par(A1,B)
	  ;   rewrite_step(B, Gamma, Delta, Rho, B1, Gamma1, Delta1, Rho1) ->
	      T1=par(A,B1)
	  )
	% seq([A|B])
	; functor(T, seq, 1) ->
	  arg(1, T, S),
	  (   S == [] ->
	      T1=skip, Gamma1=Gamma, Delta1=Delta, Rho1=Rho
	  ;   S=[A|B],
	      (  A==skip ->
		  T1=seq(B),Gamma1=Gamma, Delta1=Delta, Rho1=Rho
	      ;   rewrite_step(A, Gamma, Delta, Rho, A1, Gamma1, Delta1, Rho1) ->
		  T1=seq([A1|B])
	      )
	  )
	).

rewrite(T, Gamma, Delta, Rho, T2, Gamma2, Delta2, Rho2) :-
	(   	T=T2, Gamma=Gamma2, Delta=Delta2, Rho=Rho2
	;   rewrite_step(T, Gamma, Delta, Rho, T1, Gamma1, Delta1, Rho1) ->
	    rewrite(T1, Gamma1, Delta1, Rho1, T2, Gamma2, Delta2, Rho2)
	;   format('Failed to rewrite term:~p~n' ,[T]), fail
	).
	
		
rewrite(T, Gamma1, Delta1, Rho1) :-
	empty_avl(Gamma),
	empty_avl(Rho),
	Delta=[],
	rewrite(T, Gamma, Delta, Rho, skip, Gamma1, Delta1, Rho1).

pp_term(T, S) :-
	%% TODO
	(   functor(T, recv, 2) ->
	    arg(1, T, P),
	    arg(2, T, X),
	    format_atom('~p: ~p<-recv()', [P,X], S)
	;   functor(T, send, 3) ->
	    arg(1, T, P),
	    arg(2, T, X)
	).

%%%%%%%%%%
% Examples
%%%%%%%%%&

%Ex "Send first" P1=seq([send(e_pid(p0),e_pid(p1),p0),recv(p0,x1)]), P2=seq([send(e_pid(p1), e_pid(p0), p1), recv(p1,x1)]), T=(par(P1,P2)), rewrite(T, _, Delta1, Rho1).

%Ex: "registry"
%
%M=seq([send(e_pid(m),e_pid(p1),r),send(e_pid(m),e_pid(p2),r),recv(m,x1),send(e_pid(m),e_pid(r),m)]), R=seq([recv(r, x1),recv(r, x2),send(e_pid(r),e_pid(m),a),recv(r, x3)]), P1=seq([recv(p1, x1),send(e_pid(p1),e_var(x1),p1)]), P2=seq([recv(p2, x1),send(e_pid(p2),e_var(x1),p2)]), T= (par(M,par(par(R,P1),P2))), rewrite(T, _, Delta1, Rho1).

%%  P1=seq([send(e_pid(m),e_pid(p),m), recv(m, x1)]), P2=seq([recv(p, id), send(e_pid(p),e_var(id),p)]), T=(par(P1,P2)), rewrite(T, _, Delta1, Rho1).

%% Loops: P1=seq([send(e_pid(m),e_pid(P),m),recv(m,x)]), P2=seq([recv(P, id),send(e_pid(P),e_pid(m),m)]), T=(par(for(P, s, P1),sym(P, s, P2))), rewrite(T, _, Delta1, Rho1).