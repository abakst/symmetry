Require Export ProcessRewrite.
Require Export RewriteTactics.

Inductive Message :=
  | t1 | t2 | t3.

Parameter x y p q r : nat.

Definition p_proc :=
  s_send (p_sng q) (t1, p_sng p); s_recv (t2, p_none).

Definition q_proc :=
  s_bind (p_sng x) (s_recv (t1, p_sng x); s_send (p_sng x) (t2, p_none);
            (s_bind (p_sng y) (s_recv (t1, p_sng y); s_send (p_sng y) (t3, p_none)))).

Definition r_proc :=
  s_send (p_sng q) (t1, p_sng r); s_recv (t3, p_none).

  Ltac simpl_clocks :=
    repeat (match goal with
      | |- context[eq_dec_pidclass ?x ?x] => destruct (eq_dec_pidclass x x); [ idtac | congruence ]
      | |- context[eq_dec_pidclass ?x ?y] => destruct (eq_dec_pidclass x y); [ congruence | idtac ]
      | |- context[eq_dec_pidclass ?x ?y] => destruct (eq_dec_pidclass x y)
      | |- context[inc_my_clock] => unfold inc_my_clock at 1
      | |- context[merge_clocks] => unfold merge_clocks at 1
    end); cbn.

  Ltac simpl_clocks_h :=
    repeat (match goal with
      | H : context[eq_dec_pidclass ?x ?x] |- _ => destruct (eq_dec_pidclass x x); [ idtac | congruence ]
      | H : context[eq_dec_pidclass ?x ?y] |- _=> destruct (eq_dec_pidclass x y); [ congruence | idtac ]
      | H : context[eq_dec_pidclass ?x ?y] |- _ => destruct (eq_dec_pidclass x y)
      | H : context[inc_my_clock] |- _ => unfold inc_my_clock at 1 in H
      | H : context[merge_clocks] |- _ => unfold merge_clocks at 1 in H
    end); cbn.

Example bad :
  x <> y -> 
  x <> p -> x <> q -> x <> r ->
  y <> p -> y <> q -> y <> r ->
  p <> q -> p <> r -> q <> r -> 
  (exists t,
    RewriteRel t 
               [ p [[ p_proc ]] | q [[ q_proc ]] | r [[ r_proc ]] ]
               [ p [[ s_skip ]] | q [[ s_skip ]] | r [[ s_skip ]] ]
    /\ (~ Causal t)).
Proof.
  intros.
  eapply ex_intro.
  split.
  unfold p_proc, q_proc, r_proc.
  inst_bind 0 1.
  reduce_pair 0 1.
  inst_bind 2 1.
  reduce_pair 2 1.
  skip.
  simpl Causal.
  unfold Causal, run_clock, Causal', find_races, partition.
  simpl partition. simpl fst.
  match goal with
    | |- context[if (?b : bool) then _ else _]  => destruct b eqn:X; cbn
  end.
  intro.
  destruct H9.
  unfold ClocksLt in H10.
  destruct H10.
  destruct H11.
  simpl_clocks_h. inversion H11.
  unfold andb in X.
  unfold negb in X.
  destruct H7.
  destruct (Nat.eqb p r) eqn:Y.
  rewrite PeanoNat.Nat.eqb_eq in *.
  assumption.
  destruct X. 
  rewrite <- PeanoNat.Nat.eqb_eq in *.
  rewrite Y.
  apply PeanoNat.Nat.eqb_eq. reflexivity.
Qed.

  unfold merge_clocks at 1 in H11.
  destruct (eq_dec_pidclass (p_sng r) (p_sng p)); [ congruence | idtac ].
  
  split; auto.
  unfold ClocksLt.
  split.
  intros.
  simpl_clocks.
  auto.
  exists (p_sng r); simpl_clocks.
  ex_intro.
  simpl_clocks.
  
  unfold run_clock.
  find_races, partition.
 
  simpl event_of.
  simpl app.
  unfold Causal.
  simpl run_clock.
  cbn.
  unfold find_races.
  unfold partition.
  cbn.
  destruct (negb (Nat.eqb p r) && Nat.eqb q q)%bool. 
  simpl. split.
  unfold inc_my_clock at 1.
  unfold inc_my_clock.
  simpl.
  simpl.
  unfold find_races.
  unfold partition.
 repeat (match goal with
      (* | |- context[eq_dec_pidclass ?x ?x] => destruct (eq_dec_pidclass x x); [ idtac | congruence ] *)
      (* | |- context[eq_dec_pidclass ?x ?y] => destruct (eq_dec_pidclass x y); [ congruence | idtac ] *)
      | |- context[eq_dec_pidclass ?x ?y] => destruct (eq_dec_pidclass x y)
      | |- context[inc_my_clock] => unfold inc_my_clock at 1
      (* | |- context[merge_clocks] => unfold merge_clocks at 1 *)
    end).

  unfold inc_my_clock at 6.
  cbn.
  Ltac t H :=
    match H with
      | context G [inc_my_clock] => t G
      | _ => unfold inc_my_clock at 1
      (* | |- context[inc_my_clock] => t G *)
    end.
  match goal with
    | |- context H [inc_my_clock] => 
      let x := context H [inc_my_clock] in
      t x
  end.
 repeat (match goal with
      | |- context[eq_dec_pidclass ?x ?x] => destruct (eq_dec_pidclass x x); [ idtac | congruence ]
      | |- context[eq_dec_pidclass ?x ?y] => destruct (eq_dec_pidclass x y); [ congruence | idtac ]
      (* | |- context[eq_dec_pidclass ?x ?y] => destruct (eq_dec_pidclass x y) *)
      | |- context[inc_my_clock] => unfold inc_my_clock at 1
      (* | |- context[merge_clocks] => unfold merge_clocks at 1 *)
    end).

  simpl_clocks.
  unfold inc_my_clock at 1.
  unfold inc_my_clock at 1.
  simpl_clocks.
  unfold merge_clocks at 1. 
  destruct (eq_dec_pidclass
  simpl_clocks.