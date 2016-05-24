/* This module contains various utility predicates */

:- module(misc, [
		 bb_add_set/2,
		 bb_push/2,
		 bb_get/3,
		 bb_inc/2,
		 bb_dec/2,
		 bb_add/2,
		 retractall_predspec/1,
		 set_flag/1, 
		 if_flag/3, if_flag/2,
		 if_not_flag/3, if_not_flag/2,
		 ensure/1, ensure/2, optional/1,
		 positive_integer/1, non_negative_integer/1,
		 shell/1,shell/2,shell/3,
		 shell_measure/3,
		 shell_bg/2,
		 replace_function/5,
		 init_counter/1,increment/2,
		 setcolor/3, setcolor/4,
		 resetcolor_bw/3, resetcolor_bw/4,
		 print_color/4, print_color/5,
		 format_color/5, format_color/6,
		 all/1,
		 if2/2,
		 ord_term_variables/2,
		 list_intersection/2,
		 list_intersection/3,
		 list_partition/4,
		 choice/2,
		 foldlist/4,
		 % Atom predicates
		 format_atom/3,
		 atom_term/2,
		 atom_number/2,
		 atom_list_concat/2,
		 atom_list_append_suffix/3,
		 atom_suffix/3, atom_prefix/3,
		 timestamp/1, timestamp/2,
		 ground_term_codes/2,
		 % Easy modification of env flags
		 turn_off_warning_flags/3,
		 turn_on_warning_flags/3,
		 %opening and closing safely
		 open_file/3, % halts if fail to open
		 % tracing utils
		 trace/1,t/0,
		 % AVL predicates
		 var_subst_avl/3,
		 var_subst_list/3,
		 ord_avl_domain/2,
		 avl_domain_subtract/3,
		 avl_domain_intersection/3,
		 term_subst_avl/3,
		 avl_fetch_default/4
		], [hidden(true)]).
		 
:- use_module(library(process)).
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(ordsets)).
:- use_module(library(codesio), [format_to_codes/3, read_from_codes/2,
				 write_to_codes/2]).
:- use_module(library(system)).
:- use_module(library(timeout)).
:- use_module(library(terms)).
:- use_module(library(avl)).

timestamp(Stamp) :-
	now(When),
	make_timestamp(When, Stamp).

timestamp(When, Stamp) :-
	(   var(When) ->
	    now(When)
	;   true
	),
	make_timestamp(When, Stamp).

make_timestamp(When, Stamp) :-
	datime(When, datime(Year, Month, Day, Hour, Min, Sec)),
	zpad(Month, ZMonth),
	zpad(Day, ZDay),
	zpad(Hour, ZHour),
	zpad(Min, ZMin),
	zpad(Sec, ZSec),
	format_atom('~p-~p-~pT~p:~p:~p', [Year, ZMonth, ZDay, ZHour, ZMin, ZSec], Stamp).

zpad(Atom, ZAtom) :-
	format_atom('~`0t~p~2|', [Atom], ZAtom).

atom_list_append_suffix([N|Ns],A,[Np|Nps]):-
	atom_concat(N,A,Np),
	atom_list_append_suffix(Ns,A,Nps).
atom_list_append_suffix([],_,[]).

atom_list_concat([A|As],AccAtom,RAtom):-
	(   atom(A)->
	    A=Atom
	;   atom_term(Atom,A)
	),
	atom_concat(AccAtom,Atom,NAccAtom),
	atom_list_concat(As,NAccAtom,RAtom).
atom_list_concat([],RAtom,RAtom).

atom_list_concat(As,RAtom):-
	atom_list_concat(As,'',RAtom).

format_atom(Format, Arguments, Atom) :-
	format_to_codes(Format, Arguments, Codes),
	atom_codes(Atom, Codes).


atom_number(Atom, Number) :-
	(   var(Atom) ->
	    number_codes(Number, Codes),
	    atom_codes(Atom, Codes)
	;   atom_codes(Atom, Codes),
	    number_codes(Number, Codes)
	).
	
atom_term(Atom, Term) :-
	(   var(Atom) ->
	    write_to_codes(Term, Codes),
	    atom_codes(Atom, Codes)
	;   atom_codes(Atom, AtomCodes),
	    atom_codes('.', DotCode),
	    append(AtomCodes, DotCode, AtomDotCodes),
	    read_from_codes(AtomDotCodes, Term)
	).

atom_suffix(Atom, SuffixLen, Suffix):-
	atom_codes(Atom, Codes),
	suffix_length(Codes, SuffixCodes,SuffixLen),
	atom_codes(Suffix, SuffixCodes).
	
atom_prefix(Atom, PrefixLen, Prefix):-
	atom_codes(Atom, Codes),
	prefix_length(Codes, PrefixCodes,PrefixLen),
	atom_codes(Prefix, PrefixCodes).

/*
    == more blackboard functions ==

    bb_push(:Key, +Term)

    assumes that the current value for the given Key in the blackboard is a list, and
    adds the given term to the front of such list. If the Key is currently undefined,
    it stores a new list containing the given term as its single element.

    bb_add_set(:Key, +Term)

    same as bb_push, but assumes that the Key in the blackboard points to an ordered
    set.

    bb_get(:Key, -Term, +Default)

    a non failing version of bb_get. If the Key is not currently set in the blackboard,
    then Term is unified with the provided Default value.
*/
:- meta_predicate bb_get(:, -, +).
bb_get(Key, Term, Default) :-
	(   bb_get(Key, Term) ->
	    true
	;   Term = Default
	).

:- meta_predicate bb_push(:, +).
bb_push(Key, Term) :-
	bb_get(Key, OldList, []),
	bb_put(Key, [Term|OldList]).

:- meta_predicate bb_add_set(:, +).
bb_add_set(Key, Term) :-
	bb_get(Key, OldSet, []),
	ord_add_element(OldSet, Term, NewSet),
	bb_put(Key, NewSet).

:- meta_predicate bb_inc(:, -).
bb_inc(Key, Value) :-
	bb_get(Key, OldValue, 0),
	Value is OldValue + 1,
	bb_put(Key, Value).

:- meta_predicate bb_add(:, +).
bb_add(Key, Delta) :-
	(   bb_get(Key, Old) ->
	    true
	;   Old = 0
	),
	New is Old+Delta,
	bb_put(Key, New).

:- meta_predicate bb_dec(:, -).
bb_dec(Key, Value) :-
	bb_get(Key, OldValue, 0),
	Value is OldValue - 1,
	bb_put(Key, Value).

:- meta_predicate retractall_predspec(:).
retractall_predspec(Module:Name/Arity) :-
	functor(T, Name, Arity),
	retractall(Module:T).

:- meta_predicate set_flag(:).
set_flag(Flag) :- bb_put(Flag, 1).

:- meta_predicate if_flag(:, :, :).
if_flag(Flag, Value, Cmd) :- bb_get(Flag, Value) -> Cmd; true.

:- meta_predicate if_flag(:, :).
if_flag(Flag, Cmd) :- bb_get(Flag, 1) -> Cmd; true.

:- meta_predicate if_not_flag(:, :, :).
if_not_flag(Flag, Value, Cmd) :- bb_get(Flag, Value) -> true; Cmd.

:- meta_predicate if_not_flag(:, :).
if_not_flag(Flag, Cmd) :- bb_get(Flag, 1) -> true; Cmd.


/* executes the Call and throws an exception if the Call fails */
:- meta_predicate ensure(:, +).
ensure(Call, Except) :-
	(   Call ->
	    true
	;   throw(Except)
	).

:- meta_predicate ensure(:).
ensure(Call) :-
	(   Call ->
	    true
	;   throw(ensure_failed(Call))
	).

/* executes the Call and succeeds regardless of whether the Call succeeded or not */
:- meta_predicate optional(:).
optional(Call) :- ( Call -> true ; true).

/* `executes' all solutions of Call */
:- meta_predicate all(:).
all(Call):- findall(_, Call, _).

:- meta_predicate if2(:, :).
if2(A, B):- (A -> B; true).

ord_term_variables(T, Vars) :-
	term_variables(T, TmpVars),
	list_to_ord_set(TmpVars, Vars).
%	term_variables_set(T, Vars).

list_intersection(Lists, I) :-
	maplist(list_to_ord_set, Lists, Sets),
	ord_intersection(Sets, I).

list_intersection(Lists, I, Residues) :-
	maplist(list_to_ord_set, Lists, Sets),
	ord_intersection(Sets, I),
	(   foreach(Set, Sets),
	    foreach(Residue, Residues),
	    param(I)
	do  ord_subtract(Set, I, Residue)
	).

list_partition(Xs, Pred, Pos, Neg) :-
	foreach(X, Xs),
	fromto([], InPos, OutPos, Pos),
	fromto([], InNeg, OutNeg, Neg),
	param(Pred)
	do
	(   call(Pred, X) ->
	    OutPos = [X|InPos],
	    OutNeg = InNeg
	;   OutPos = InPos,
	    OutNeg = [X|InNeg]
	).

choice(ChoiceSets, ChoicesSet) :-
	term_variables(ChoiceSets, Vars),
	findall(Choices-Vars,
		(   foreach(ChoiceSet, ChoiceSets),
		    foreach(Choice, Choices)
		do  member(Choice, ChoiceSet)
		), AllChoicesVars),
	(   foreach(Choices-Vars, AllChoicesVars),
	    foreach(Choices, ChoicesSet),
	    param(Vars)
	do  true
	).

:- meta_predicate foldlist(:, +, +, -).
foldlist(Pred, Xs, V0, V) :-
	foreach(X, Xs),
	fromto(V0, In, Out, V),
	param(Pred)
	do
	call(Pred, X, In, Out).

/* simple type checks, useful for maplist and friends */
positive_integer(T) :-
	integer(T),
	T > 0.

non_negative_integer(T) :-
	integer(T),
	T >= 0.

shell(Cmd) :-
	(   environ('OS', 'Windows_NT') -> % sorry, timeouts via "ulimit -t 900" do not work in Cygwin-Windows
	    shell(Cmd, exit(0))
	;   timeout:'$stop_timer_a'(TargetTime),
	    (   TargetTime = off ->
		shell(Cmd, exit(0))
	    ;	timeout:'$timer_now'(TimeNow),
		TimeLeft is TargetTime-TimeNow,
		TimeLeftSec is round(TimeLeft/1000),
		shell(Cmd, Status, TimeLeftSec, ProcessTime),
		FinalTimeLeft is TimeLeft-ProcessTime,
		FinalTargetTime is TargetTime-ProcessTime,
		timeout:start_timer(FinalTargetTime,FinalTimeLeft),
		(   Status = exit(0) ->
		    true
		;   FinalTimeLeft > 0 ->
		    false
		;   true
		)
	    )
	).

shell_measure(Cmd, Status, TimeTaken) :-
	statistics(walltime, [StartWallTime|_]),
	shell(Cmd, Status),
	statistics(walltime, [FinishWallTime|_]),
	TimeTaken is FinishWallTime-StartWallTime.

shell(Cmd, Status, TimeOut) :-
	format_atom('ulimit -t ~p && ~p', [TimeOut, Cmd], FCmd),
	shell(FCmd, Status).

shell(Cmd, Status) :-
	(   environ('OS', 'Windows_NT') ->
	    process_create(path(cmd), ['/C', Cmd], [process(Proc)])
	;   absolute_file_name('$SHELL', Shell),
	    process_create(Shell,
			   ['-c', Cmd],
			   [stdout(std), stderr(std), process(Proc)])
	),
	process_wait(Proc, Status).

shell_bg(Cmd, Process) :-
	absolute_file_name('$SHELL', Shell),
	process_create(Shell,
		       ['-c', Cmd],
		       [stdout(std), stderr(std), process(Process)]).

replace_function(T, Old, Arity, New, NewT) :-
	(   simple(T) ->
	    NewT = T
	;   T =.. [Name|Args] ->
	    (   Name = Old, length(Args, Arity) ->
		NewT =.. [New|Args]
	    ;   replace_functions(Args, Old, Arity, New, NewArgs),
		NewT =.. [Name|NewArgs]
	    )
	).
replace_functions([T|Ts], Old, Arity, New, [NewT|NewTs]) :-
	replace_function(T, Old, Arity, New, NewT),
	replace_functions(Ts, Old, Arity, New, NewTs).
replace_functions([], _, _, _, []).


init_counter(Counter) :- bb_put(Counter, 0).
increment(Counter, NextValue) :- bb_inc(Counter, NextValue).

% list_to_assoc([X1-(X-1), Y-5], Map), subst([X1>=0, Y1=Z], Map, Output).

% TODO what to do which cascading update: I1=I+1, I2=I1+10? Apply them in 'layers' following the composition of statements!!!
% list_to_assoc([I1-(I+1), I2-(I1+10)], Map), subst([X1>=0, Y1=Z], Map, Output).


obsolete_subst(Input, SubstMap, Output) :-
	(   get_assoc(Input, SubstMap, Output) ->
	    true
	;   compound(Input) ->
	    % TODO: use for each arg
	    Input =.. [SubSymbol|SubInputs],
	    subst_list(SubInputs, SubstMap, SubOutputs),
	    Output =.. [SubSymbol|SubOutputs]
	;   Output = Input
	).
obsolete_subst_list([SubInput|SubInputs], SubstMap, [SubOutput|SubOutputs]) :-
	subst(SubInput, SubstMap, SubOutput),
	subst_list(SubInputs, SubstMap, SubOutputs).
obsolete_subst_list([], _, []).

/*

mapterm(+LeafModule:LeafPred, +NodeModule:NodePred, +OldTerm, -NewTerm).

LeafModule:LeafPred(+OldLeaf, -NewLeaf)
NodeModule:NodePred(OldFunctor, OldParamList, NewNode)
or NodePred = _:id

Example:
eqPred(X, X).
xxx(f, [A, B], wf(s(A), s(B))).

| ?- mapterm(user:eqPred, user:xxx, f(a, B), T).
T = wf(s(a),s(B)) ? 
yes

*/
obsolete_mapterm(LeafModule:LeafPred, NodeModule:NodePred, OldTerm, NewTerm) :-
	(   (   var(OldTerm)
	    ;   atomic(OldTerm)
	    ) ->
	    (   LeafPred == id ->
		OldTerm = NewTerm
	    ;   NodeCall =.. [LeafPred, OldTerm, NewTerm],
		call(LeafModule:NodeCall)
	    )
	;   OldTerm =.. [OldTermName|OldSubTerms],
	    % TODO use for each arg
	    mapterms(OldSubTerms, LeafModule:LeafPred, NodeModule:NodePred, NewSubTerms),
	    (   NodePred == id ->
		NewTerm =.. [OldTermName|NewSubTerms]
	    ;   NodeCall =.. [NodePred, OldTermName, NewSubTerms, NewTerm],
		call(NodeModule:NodeCall)
	    )
	).
obsolete_mapterms([OldTerm|OldTerms], LeafPred, NodePred, [NewTerm|NewTerms]) :-
	mapterm(LeafPred, NodePred, OldTerm, NewTerm),	
	mapterms(OldTerms, LeafPred, NodePred, NewTerms).
obsolete_mapterms([], _, _, []).

obsolete_var_count(Term,Count) :- var_count([Term],[],0,_,Count). 
obsolete_var_count(Term,Vars,Count) :- var_count([Term],Vars,0,_,Count).
obsolete_var_count([],Vars,VarCount,Vars,VarCount).
obsolete_var_count([Term|Terms],Vars,VarCount,Nvars,NVarCount):-
	(   var(Term)->
	    (   term_match(Vars,Term) ->
		Nvs = Vars,
		NC = VarCount
	    ;	Nvs = [Term|Vars],
	        NC is VarCount + 1
	    )
	;   Term =.. [_|Ts],
	    var_count(Ts,Vars,VarCount,Nvs,NC)
	),
	var_count(Terms,Nvs,NC,Nvars,NVarCount).


attr_code(reset, 0).
attr_code(bright, 1).
attr_code(dim, 2).
attr_code(underline, 3).
attr_code(blink, 4).
attr_code(reverse, 7).
attr_code(hidden, 8).

color_code(black, 0).
color_code(red, 1).
color_code(green, 2).
color_code(yellow, 3).
color_code(blue, 4).
color_code(magenta, 5).
color_code(cyan, 6).
color_code(white, 7).

setcolor(Attr, Foreground, Background) :-
	setcolor(user_output, Attr, Foreground, Background).
setcolor(Stream, Attr, Foreground, Background) :-
	attr_code(Attr, AttrCode),
	color_code(Foreground, ForegroundCode),
	color_code(Background, BackgroundCode),
	ForegroundId is ForegroundCode+30,
	BackgroundId is BackgroundCode+40,
	format(Stream, '~c[~d;~d;~dm', [27, AttrCode, ForegroundId, BackgroundId]).

print_color(Data, Attr, Foreground, Background) :-
	print_color(user_output, Data, Attr, Foreground, Background).
print_color(Stream, Data, Attr, Foreground, Background) :-
	format_color(Stream, '~p', [Data], Attr, Foreground, Background).
format_color(Format, Data, Attr, Foreground, Background) :-
	format_color(user_output, Format, Data, Attr, Foreground, Background).
format_color(Stream, Format, Data, Attr, Foreground, Background) :-
	setcolor(Stream, Attr, Foreground, Background),
	format(Stream, Format, Data),
	setcolor(Stream, reset, white, black).

ground_term_codes(T, Cs) :-
	(   number(T) ->
	    number_codes(T, Cs)
	;   T =.. [Name|Ts],
	    atom_codes(Name, NameCs),
	    (   Ts = [] ->
		Cs = NameCs
	    ;	maplist(ground_term_codes, Ts, TsCsList),
		append(TsCsList, TsCs),
		atom_codes('()', [Open, Close]),
		append([NameCs, [Open], TsCs, [Close]], Cs)
	    )
	).

turn_off_warning_flags(F1, F2, F3) :-
	prolog_flag(single_var_warnings, F1, off),
	prolog_flag(syntax_errors, F2, error),
	prolog_flag(discontiguous_warnings, F3, off).

turn_on_warning_flags(F1, F2, F3) :-
	prolog_flag(single_var_warnings, _, F1),
	prolog_flag(syntax_errors, _, F2),
	prolog_flag(discontiguous_warnings, _, F3).


open_file( File, Mode, Out ):-
	catch( open( File, Mode, Out), _,
	       ( format('#Failed To Open ~p\n',[Out] ), halt)
	     ).


trace(C):- C,!,trace.
trace(_).


% AVL predicates

var_subst_avl(P, M, Q) :-
	avl_to_list(M, VsEs),
	var_subst_list(P, VsEs, Q).

var_subst_list(P, VsEs, Q) :-
	keys_and_values(VsEs, Vs, Es),
	list_to_ord_set(Vs, VS),
	ord_term_variables(P, PVarS),
	ord_subtract(PVarS, VS, RestVarS),
	copy_term(P-RestVarS-Vs, Q-RestVarS-Es).

ord_avl_domain(AVL, VarS) :-
	avl_domain(AVL, Vars),
	list_to_ord_set(Vars, VarS).

avl_domain_subtract(AVL, Vs, R) :-
	foreach(V, Vs),
	fromto(AVL, In, Out, R)
	do
	(   avl_delete(V, In, _, Out) ->
	    true
	;   Out = In
	).

avl_domain_intersection(AVL, Vs, R) :-
	list_to_ord_set(Vs, VS),
	avl_domain(AVL, Ds),
	list_to_ord_set(Ds, DS),
	ord_subtract(DS, VS, DsNotVs),
	avl_domain_subtract(AVL, DsNotVs, R).

/* top down pass. creates a copy, i.e., not in-place. */
term_subst_avl(T, M, R) :-
	(   avl_fetch(T, M, R) ->
	    true
	;   compound(T) ->
	    functor(T, Sym, Arity),
	    functor(R, Sym, Arity),
	    (   foreacharg(TI, T),
		foreacharg(RI, R),
		param(M)
	    do  term_subst_avl(TI, M, RI)
	    )
	;   R = T
	).

avl_fetch_default(Key, AVL, Value, Default) :-
	(   avl_fetch(Key, AVL, Value) ->
	    true
	;   Value = Default
	).