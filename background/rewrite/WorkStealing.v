Require Export ProcessRewrite.
Require Export RewriteTactics.
Import ListNotations.
Open Scope stmt.

Inductive Message :=
  | int
  | id
  | tt.

Parameters me q : pid.
Parameters x y xs ps : Var.
Parameters X : MuVar.
Hypothesis H : measure xs = measure ps.
Hypothesis G : me <> q.
Hypothesis I : x <> y.

Definition worker_loop :=
  [[ s_send (p_sng q) (id, p_set ps); s_recv (int, p_none); s_send (p_sng me) (int, p_none); s_var X ]].

Example WorkStealing0 :
    [ q   @ [[ s_iter xs (s_recv_x (id, x) (s_send (p_var x) (int, p_none))) ]]
    ; {ps}@ [[ s_loop X worker_loop ]]
    ; me  @ [[ s_iter xs (s_recv (int, p_none)) ]]
    ] 
      ===> 
    [ q   @ [[ s_skip ]]
    ; {ps}@ [[ s_loop X worker_loop ]]
    ; me  @ [[ s_skip ]]
    ].
Proof.
  begin.
  (** Protocol **)
  unfold worker_loop.
  rewrite_eq_stmt 1.
  apply stmt_unfold_loop.
  inst_bind 0.
    destruct x.
    destruct (Nat.eqb n n) eqn:Foo.
    Focus 2.
    rewrite PeanoNat.Nat.eqb_neq in Foo.
    congruence.
  reduce_choice 1 0 1.
  reduce_pair 0 1.
  reduce_pair 1 2.
  rewrite_eq_stmt 1.
  apply stmt_fold_loop.
  skip. 
  (** Causality **)
  trust_me_its_causal.
Qed.

Definition sendn {T:Type} p m := @s_send T p (m, p_none).
Definition recvn {T:Type} m := @s_recv T (m, p_none).

Definition recvs (s1 s2 : Stmt) :=
  s_recv_l [((int,p_none), s1); ((tt,p_none), s2)].

Definition me_body := recvs (recvs s_skip s_skip) (recvs s_skip s_skip).

Example choice0 :
  [ q  @ [[ s_iter xs [[sendn (p_sng me) int; sendn (p_sng me) tt]] ]]
  ; me @ [[ s_iter xs me_body ]]
  ] ===>
  [ q  @ [[ s_skip ]] 
  ; me @ [[ s_skip ]]
  ].
Proof.
  (** Rewrite **)
  begin.
  reduce_choice 0 1 0.
  reduce_choice 0 1 1.
  skip.
  (** Causality **)
  trust_me_its_causal.
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
  [ q @ [[ s_iter xs
             (s_recv_x (id, x)
              (s_send (p_var x) (int, p_none)));
           s_loop X (s_recv_x (id, y) 
                      [[ s_send (p_var y) (tt, p_none);
                         s_var X ]]) ]]
  ;{ps} @ [[ s_loop X [[ s_send (p_sng q) (id, p_set ps);
                        s_recv_l [ (int,p_none, 
                                    [[ s_send (p_sng me) (int, p_none); 
                                       s_var X ]])
                                 ; (tt, p_none, s_skip)
                                 ] ]] ]]
  ; me @ [[ s_iter xs (s_recv (int, p_none)) ]] ] ===>
  [ q @ [[ s_loop X (s_recv_x (id, y) 
                    [[ s_send (p_var y) (tt, p_none); s_var X ]]) ]]
   ; { ps } @ [[ s_skip ]] ; me @ [[ s_skip ]] ].
Proof.
  begin.
Ltac inst_bind x :=
  eapply rewrite_trans;
    [eapply rewrite_bind with (i := x); cbn; try reflexivity | idtac]; 
     auto.
  inst_bind 0.
  simpl inst_stmt.
  assert (eqb_var x y = false).
    admit.
  destruct (eqb_var x y); [congruence | auto].
  destruct (eqb_var x x) eqn : FOO. 
  kill_substs.
  rewrite_eq_stmt 1.
  apply stmt_unfold_loop.
  reduce_choice 1 0 1.
  reduce_choice 0 1 0.
  reduce_pair 1 2.
  rewrite_eq_stmt 1.
  apply stmt_fold_loop.
  rewrite_eq_stmt 0.
  apply stmt_unfold_loop.
  rewrite_eq_stmt 1.
  apply stmt_unfold_exit.
  inst_bind 0.
  simpl inst_stmt.
  destruct (eqb_var y y) eqn:XXX.
  cbn. kill_substs.
  reduce_choice 1 0 1.
  reduce_choice 0 1 1.
  rewrite_eq_stmt 1.
  apply stmt_exit_loop.
  rewrite_eq_stmt 0.
  apply stmt_fold_loop.
  skip.
  admit.
  admit.
  simpl.
  trust_me_its_causal.
  unfold ClocksLt.
  split.
  intros.
  unfold merge_clocks.
  simpl. 
  destruct (eq_dec_pidclass (p_sng q) (p_sng q)) eqn: FOO.
  unfold inc_my_clock. simpl.
  destruct (eq_dec_pidclass (p_set ps) (p_sng q)) eqn: FOO2.

  reduce_pair 0 1.
  reduce_pair 0 1.
  choose_left 1.
  reduce_pair 0 1.
  reduce_pair 1 2.