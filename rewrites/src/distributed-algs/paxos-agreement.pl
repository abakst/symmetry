/*
// [[ A ]] : A is atomic.

sym p in P do
   for a in A do a.w<-⊥;
   p.v<-*; p.Ho=0;
   for a in A do
   [[
      if a.w = ⊥ then
         a.w <- p.v
      end;
      if a.w=p.v && * then
	 p.Ho <- p.Ho+1
      end
   ]]
   end
end
Prove: forall p,p' in P: p.Ho>1/2 /\ p'.Ho>1/2 => p.v=p'.v
*/

query_naming(inv(p_v, a_w, p_ho, k, l, _)).
%preds(inv(V, W, Ho, K, L, _),[K>=L+Ho,K>=Ho]).

%%% TODO: might not hear of a thread.

%% Globals:  a.w
%% Locals :  p.v, p.HO
%% Aux    :  k(p) = #{a in A | a.w=p.v}
%% Aux    :  l(p) = #{a in A | a.w=p.v /\ a \not in Ho(p)}

%% Derived invariant: forall p in P: p.ho+l(p)=<k(p),p_ho(p)=<k(p)

%% Initial
inv(V, W, Ho, K, L, _) :- Ho=0, K=0, W= -1, L=0, V>=0.

%% Transition relation:
next(V, W, Ho, W1, Ho1) := ite(W<0, W1=V, W1=W), ite(W1=V, Ho1=Ho+1, Ho1=Ho).

%% The invariants tracks locals for nodes p in P and a in A.
%% Case splits are on whether the updates are performed
%% by a and p or other nodes.

%% Case 1: p updates a
inv(V, W1, Ho1, K1, L2, _) :-
	inv(V, W, Ho, K, L, _),
	next(V, W, Ho, W1, Ho1),
	%% counting
	ite(W<0, (K1=K+1,L1=L+1), (K1=K,L1=L)),
	ite(W1=V, L2=L1-1, L2=L1),
	L2>=0.

%% Case 2: p updates ap =\= a.
inv(V, W, Ho1, K1, L2, _) :-
	inv(V, W, Ho, K, L, _),
	inv(V, Wp, Ho, K, L, _),
	next(V, Wp, Ho, Wp1, Ho1),
	%% counting
	ite(Wp<0,(K1=K+1,L1=L+1),(K1=K,L1=L)),
	ite(Wp1=V, L2=L1-1, L2=L1),
	L2>=0.

%% Case 3: pp =\=p updates a.
inv(V, W1, Ho, K1, L1, _) :-
	inv(V, W, Ho, K, L, _),
	inv(Vp, W, _, _, _, _),
	next(Vp, W, _, W1, _),
	%% counting
	ite(W1=V, (K1=K+1,L1=L+1), (K1=K,L1=L)).

%% Case 4: pp =\=p updates ap =\= a.

inv(V, W, Ho, K1, L1, _) :-
	inv(V, W, Ho, K, L, _),
	inv(Vp, Wp, _, _, _, _),
	next(Vp, Wp, _, Wp1, _),
	ite(Wp1=V, (K1=K+1,L1=L+1), (K1=K,L1=L)).

% Lemmas:
K>=L+Ho :- inv(V, W, Ho, K, L, _).
K>=Ho   :- inv(V, W, Ho, K, L, _).

% Property:
V1=V2 :-
	inv(V1, W, Ho1, K1, L, _),
	inv(V2, W, Ho2, K2, L, _),
	Ho1>N/2, Ho2>N/2,
	(K1+K2>N->V1=V2).
