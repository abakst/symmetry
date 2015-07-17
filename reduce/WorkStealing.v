Require Export ProcessRewrite.
Require Export RewriteTactics.

Inductive Message :=
  | int
  | id
  | tt.

Parameters me q x : pid.
Parameters xs ps : SetVar.
Parameters X : MuVar.
Hypothesis H : measure xs = measure ps.
Hypothesis G : me <> q /\ me <> x /\ q <> x.

Definition worker_loop :=
  s_send (p_sng q) (id, p_set ps); s_recv (int, p_none); s_send (p_sng me) (int, p_none); s_var X.

Example WorkStealing0 :
    [ q    [[ s_iter xs (x ~ (s_recv(id, p_sng x); 
                              s_send (p_sng x) (int, p_none))) ]]
    | {ps} [[ s_loop X worker_loop ]]
    | me   [[ s_iter xs (s_recv (int, p_none)) ]]
    ] 
      ===> 
    [ q    [[ s_skip ]]
    | {ps} [[ s_loop X worker_loop ]]
    | me   [[ s_skip ]]
    ].
Proof.
  intros.
  inst_bind 0.
  rewrite_eq_stmt 1.
  apply stmt_unfold_loop.
  reduce_pair 0 1.
  reduce_pair 0 1.
  reduce_pair 1 2.
  rewrite_eq_stmt 1.
  apply stmt_fold_loop.
  skip.
Qed.

Definition sendn {T:Type} p m := @s_send T p (m, p_none).
Definition recvn {T:Type} m := @s_recv T (m, p_none).

Example choice0 :
  [ q [[ s_iter xs (sendn (p_sng me) int; sendn (p_sng me) tt) ]]
  | me[[ s_iter xs (s_ext_ch (recvn int) (recvn tt);
                    s_ext_ch (recvn int) (recvn tt)) ]]
  ] ===>
  [ q [[ s_skip ]] 
  | me[[ s_skip ]]
  ].
Proof.
  choose_left 1.
  reduce_pair 0 1.
  choose_right 1.
  reduce_pair 0 1.
  skip.
Qed.

(** 
< q             ▹ foreach (i ∈ [1..n]):
                                 ∀p. recv(p); send(p, Integer);
                               μX. ∀p. recv(p); send(p, tt); X
               p[len slaves] ▹ μX. send(q, me); { recv(Int); send(me, Int); X
                                                , recv(tt)
                                                };
               me            ▹ foreach (i ∈ [1..n]):
                                 recv(Integer)
             > Integer
**)

(** Wait how come this works? What if the last line was 1..n+1? **)
(** I think the answer is that the "context" is the product of the number
    of grouped process and the loop, thus the loop is unrolled Y times 
    such that len slaves * Y = n. So a loop unrolling must be rewritten
    into an iter before progress can be made **)

Example WorkStealing :
  [ q   [[ s_iter xs (x ~ (s_recv (id, p_sng x);
                         s_send (p_sng x) (int, p_none)));
           s_loop X (x ~ (s_recv (id, p_sng x);
                          s_send (p_sng x) (tt, p_none);
                          s_var X)) ]]
  |{ps} [[ s_loop X (s_send (p_sng q) (id, p_set ps);
                     s_ext_ch (s_recv (int, p_none); s_send (p_sng me) (int, p_none); s_var X)
                              (s_recv (tt, p_none))) ]]
  | me  [[ s_iter xs (s_recv (int, p_none)) ]] ] ===>
 [ q [[ s_skip ]] | { ps } [[ s_skip ]] | me [[ s_skip ]] ].
Proof.
  inst_bind 0.
  rewrite_eq_stmt 1.
  apply stmt_unfold_loop.
  reduce_pair 0 1.
  choose_left 1.
  reduce_pair 0 1.
  reduce_pair 1 2.
  rewrite_eq_stmt 1.
  apply stmt_fold_loop.