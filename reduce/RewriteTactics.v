Require Export ProcessRewrite.

Ltac skip := solve[apply rewrite_refl].

Ltac apply_rewrite x :=
  eapply rewrite_trans; [ x | idtac].

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

Ltac inst_bind i x :=
  eapply rewrite_trans; [
    eapply rewrite_bind with (1 := i) (3 := x); simpl; try reflexivity
    | expand_subst].
