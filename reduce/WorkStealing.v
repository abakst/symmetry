Require Export ProcessRewrite.
Require Export RewriteTactics.
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