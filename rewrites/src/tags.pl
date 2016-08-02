:- use_module(library(ordsets)).
:- use_module(library(terms)).

:- use_module('lib/misc.pl', [
			      fresh_pred_sym/1
			     ]
	     ).

/*
tag(a, t): action a has tag t.
*/

:- dynamic tags/2,   /* tags(P-Q, Tags): sends with tags
	                Tags were sent on channel P-Q.
		     */
	proc/2,      /* proc(Tag, Proc): Tag "Tag" belongs to process p. */
	sym_set/1.   /* sym_set(S): S is a set of symmetric processes. */

cleanup :-
	retractall(tags(_,_)),
	retractall(proc(_,_)),
	retractall(sym_set(_)).


tag_sends(T, Proc, T1) :-
/*
Recursively traverses T and transforms each send S into tag(S, Tag), where Tag is a fresh constant. While tagging, it updates the data-structures described in the dynamic predicates above. Proc either contains var(P, S) to indicate that variable P is bound to a process in set S, or none otherwise.
*/
	(   simple(T) ->
	    T1=T
	;   functor(T, send, 3) ->
	    T=send(P, X, _),
	    fresh_pred_sym(Tag),
	    T1=tag(T, Tag),
	    (   X=e_pid(Q) ->
		true
	    ;   X=e_var(_) ->
		true
	    ),
	    sub_sym_set(P, Proc, P1),
	    sub_sym_set(Q, Proc, Q1),
	    assert(proc(Tag, P1)),
	    assert(tags(P1-Q1, [Tag]))
	;   functor(T, sym, 3) ->
	    T=sym(P, S, A),
	    assert(sym_set(S)),
	    tag_sends(A, var(P, S), A1),
	    T1=sym(P, S, A1)
	;   functor(T, for, 4) ->
	    T=for(M, P, S, A),
	    assert(sym_set(S)),
	    tag_sends(A, var(P, S), A1),
	    T1=for(M, P, S, A1)
	;   same_functor(T, T1),
	    (   foreacharg(Arg, T),
		foreacharg(Arg1, T1),
		param(Proc)
	    do  tag_sends(Arg, Proc, Arg1)
	    )
	).

tag_recvs(T, Proc, T1) :-
/*
Tag each receive with all tags on the appropriate channel.
*/
	(   simple(T) ->
	    T1=T
	;   functor(T, recv, 2) ->
	    T=recv(P, _),
	    sub_sym_set(P, Proc, P1),
	    findall(Tags, (tags(Q-P1,Tags), Q\=P1), Tagsets),
	    ord_union(Tagsets, Tagset),
	    T1=tag(T, Tagset)
	;   functor(T, recv, 3) ->
	    T=recv(P, X, _),
	    sub_sym_set(P, Proc, P1),
	    (   X=e_pid(Q) ->
		true
	    ;   X=e_var(_) ->
		true
	    ),
	    sub_sym_set(Q, Proc, Q1),
	    findall(Tags, (tags(Q1-P1,Tags), Q1\=P1), Tagsets),
	    ord_union(Tagsets, Tagset),
	    T1=tag(T, Tagset)
	;   functor(T, sym, 3) ->
	    T=sym(P, S, A),
	    tag_recvs(A, var(P, S), A1),
	    T1=sym(P, S, A1)
	;   functor(T, for, 4) ->
	    T=for(M, P, S, A),
	    tag_recvs(A, var(P, S), A1),
	    T1=for(M, P, S, A1)
	;   same_functor(T, T1),
	    (   foreacharg(Arg, T),
		foreacharg(Arg1, T1),
		param(Proc)
	    do  tag_recvs(Arg, Proc, Arg1)
	    )
	).


sub_sym_set(P, Proc, P1) :-
	/*
	If P belongs to a symmetric set S, then P1=S, and P1=P, otherwise.
	*/
	(   Proc=var(Q, S),
	    Q==P->
	    P1=S
	;   P1=P
	).

tag_term(T, T2)	:-
	cleanup,
	tag_sends(T, none, T1),
	tag_recvs(T1, none, T2).

check_race_freedom(T, T1) :-
	tag_term(T, T1),
	check_tags(T1).
