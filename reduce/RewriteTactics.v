Require Export ProcessRewrite.

Hint Constructors EqStmt : eqstmt.

Ltac skip := solve[apply rewrite_refl].

Ltac rewrite_eq_stmt x :=
  eapply rewrite_trans; 
  [ eapply rewrite_eq_stmt with (i := x ); cbv; try reflexivity | idtac]; 
  try reflexivity; cbv.

Ltac reduce_pair i j :=
  eapply rewrite_trans;
    [apply rewrite_pair with (i1 := i) (i2 := j); try reflexivity | idtac]; cbv; auto.

Ltac expand_subst :=
  simpl; simpl inst_stmt; simpl subst_stmt; unfold subst_pid_m, subst_pid;
    repeat match goal with
             | |- context[eq_dec_pid ?x ?x] =>
               destruct (eq_dec_pid x x); [ idtac | congruence]
             | |- context[eq_dec_pid ?x ?y] =>
               destruct (eq_dec_pid x y); [ congruence | idtac]
           end.

Ltac inst_bind x :=
  eapply rewrite_trans; [
      eapply rewrite_bind with (i := x)
    | idtac ]; simpl; try reflexivity; expand_subst.

Ltac choose_left x :=
  eapply rewrite_trans; 
  [ eapply rewrite_ext_choice_l with (i := x); try reflexivity | idtac];
  simpl. 

Ltac choose_right x :=
  eapply rewrite_trans; 
  [ eapply rewrite_ext_choice_r with (i := x); try reflexivity | idtac];
  simpl. 
