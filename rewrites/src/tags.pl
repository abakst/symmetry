:- module(tags, [
		 fresh_pred_sym/1,
		 tag_recvs/3,
		 check_tags/1,
		 tag_term/2,
		 check_race_freedom/2
		 ], [hidden(false)]).

:- use_module(library(ordsets)).
:- use_module(library(terms)).
:- use_module('lib/misc.pl', [ fresh_pred_sym/1]).

/*
tag(a, t): action a has tag t.
*/

:- dynamic tags/2,   /* tags(P-Q, Tags): sends with tags
	                Tags were sent on channel P-Q.
		     */
	proc/2,      /* proc(Tag, Proc): Tag "Tag" belongs to process p. */
	type/2,      /* type(Tag, Type): Tag "Tag" belongs to a send of type "Type".  */
	sym_set/1.   /* sym_set(S): S is a set of symmetric processes. */

cleanup :-
	retractall(tags(_,_)),
	retractall(proc(_,_)),
	retractall(type(_,_)),
	retractall(sym_set(_)).


tag_sends(T, Proc, T1) :-
/*
Recursively traverses T and transforms each send S into tag(S, Tag), where Tag is a fresh constant. While tagging, it updates the data-structures described in the dynamic predicates above. Proc either contains var(P, S) to indicate that variable P is bound to a process in set S, or none otherwise.
*/
	(   simple(T) ->
	    T1=T
	;   (   functor(T, send, 3) ->
		T=send(P, X, _)
	    ;   functor(T, send, 4) ->
		T=send(P, X, Type, _)
	    ) ->
	    fresh_pred_sym(Tag),
	    (   nonvar(Type)->
		assert(type(Tag, Type))
	    ;   true
	    ),
	    (   X=e_pid(Q) ->
		true
	    ;   X=e_var(_) ->
		true
	    ;  throw(parse-pid-error(X))
	    ),
	    sub_sym_set(P, Proc, P1),
	    sub_sym_set(Q, Proc, Q1),
	    assert(proc(Tag, P1)),
	    assert(tags(P1-Q1, Tag)),
	    T1=tag(T, Tag)
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
	    findall(Tag, (tags(Q-P1,Tag), Q\=P1), Tags),
	    T1=tag(T, Tags)
	;   (   functor(T, recv, 3) ->
		T=recv(P, X, _)
	    ;   functor(T, recv, 4) ->
		T=recv(P, X, Type, _)
	    ),
	    sub_sym_set(P, Proc, P1),
	    (   X=e_pid(Q) ->
		true
	    ;   X=e_var(_) ->
		true
	    ;   X=type(Type) ->
		true
	    ;  throw(parse-pid-error(X))
	    ),
	    sub_sym_set(Q, Proc, Q1),
	    findall(Tag, (tags(Q1-P1,Tag), Q1\=P1, (nonvar(Type)->type(Tag, Type);true)), Tags)->
	    T1=tag(T, Tags)
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

check_tags(T) :-
/*
Checks if all receive tag-sets either
 a)  consist of a single tag or
 b)  constist of tags from the same process and that process is not symmetric.
*/
	(   simple(T) ->
	    true
	;   functor(T, tag, 2),
	    T=tag(Rec, Tags),
	    functor(Rec, recv, _) ->
	    T=tag(Rec, Tags),
	    (   Tags=[Tag]->
		true
	    ;   (   foreach(Tag, Tags),
		    param(Proc, T)
		do  proc(Tag, Proc),
		    \+sym_set(Proc) ->
		    true
		;   throw(race-condition(T))
		)
	    )
	;   (   foreacharg(Arg, T)
	    do  check_tags(Arg)
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
	portray_clause(T1),
	check_tags(T1).
