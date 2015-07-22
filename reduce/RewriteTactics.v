Require Export ProcessRewrite.
Import ListNotations.
Require Import PeanoNat.
Require Import Nat.
Require Import Bool.

Hint Constructors EqStmt : eqstmt.

Ltac begin := intros; eapply ex_intro; split.
Ltac skip := solve[apply rewrite_refl].

Open Scope stmt.
Open Scope list.
Open Scope config.

Ltac rewrite_eq_stmt x :=
  eapply rewrite_trans; 
  [ eapply rewrite_eq_stmt with (i := x ); cbv; try reflexivity | idtac]; 
  try reflexivity; cbv.

Ltac reduce_pair i j :=
  eapply rewrite_trans;
    [apply rewrite_pair with (i1 := i) (i2 := j); try reflexivity | idtac]; cbv; auto.

Lemma break_if_pidclass :
  forall (x : PidClass), 
    eqb_pidclass x x = false -> False.
Proof.
  intro.
  unfold eqb_pidclass.
  destruct x; 
  try rewrite Nat.eqb_refl in *; intuition.
  destruct v. 
  unfold eqb_var in *.
  try rewrite Nat.eqb_refl in *; intuition.
  destruct v. 
  unfold eqb_var in *.
  try rewrite Nat.eqb_refl in *; intuition.
Qed.

Lemma break_if_pidclass_neg :
  forall (x y : PidClass), 
    x <> y ->
    eqb_pidclass x y = true -> False.
Proof.
  intro.
  unfold eqb_pidclass.
  destruct x; destruct y;
  try rewrite Nat.eqb_refl in *; intuition.
  apply H.
  f_equal.
  rewrite <- Nat.eqb_eq.
  exact H0.
  destruct v; destruct v0. 
  apply H.
  repeat f_equal.
  rewrite <- Nat.eqb_eq.
  exact H0.
  destruct v; destruct v0. 
  apply H.
  repeat f_equal.
  rewrite <- Nat.eqb_eq.
  exact H0.
Qed.

Ltac kill_substs :=
  simpl; simpl inst_stmt; simpl subst_stmt; unfold subst_pid_m, subst_pid;
 repeat (
     match goal with
       | |- context[eqb_pidclass ?x ?x] =>
         let H := fresh "Kill_eqb" in
         destruct (eqb_pidclass x x) eqn: H; [ auto | 
          exfalso; eauto using break_if_pidclass]; clear H
     end
   ).

Ltac defeat_eqs :=
  match goal with
    | |- context[eq_dec_pid ?x ?x] => destruct (eq_dec_pid x x); [ auto | congruence ]; cbn
    | |- context[eq_dec_pid ?x ?y] => destruct (eq_dec_pid x y); [ congruence | auto ]; cbn
  end.

Ltac inst_bind x :=
  eapply rewrite_trans;
    [eapply rewrite_bind with (i := x); cbn; try reflexivity | idtac]; 
    cbn; auto; kill_substs.

Ltac reduce_choice x y z :=
  eapply rewrite_trans; 
  [ eapply rewrite_choice with (i := x) (j := y) (k := z); cbv | idtac ]; try reflexivity; cbv; auto.

(* Ltac choose_left x := *)
(*   eapply rewrite_trans;  *)
(*   [ eapply rewrite_ext_choice_l with (i := x); try reflexivity | idtac]; *)
(*   simpl.  *)

(* Ltac choose_right x := *)
(*   eapply rewrite_trans;  *)
(*   [ eapply rewrite_ext_choice_r with (i := x); try reflexivity | idtac]; *)
(*   simpl.  *)

Ltac trust_me_its_causal :=
  unfold Causal, Causal', NoRaces; cbn;
  repeat ( 
      match goal with
        | H : @In _ _ [] |- _ => inversion H
        | H : _ /\ _ |- _ => decompose [and or] H; clear H
        | H : @In _ _ _ |- _ =>
          apply in_inv in H; destruct H; subst; cbn; intros
        | |- context[Forall _ _]  =>
          rewrite Forall_forall; split; intros
      end; try congruence
    ); auto.