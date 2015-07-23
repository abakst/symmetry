Require Export ProcessRewrite.
Require Export RewriteTactics.

Example SillyLoop :
  forall (p q : nat) (x : MuVar) (ps : SetVar),
    [ p [[ s_loop x (s_send (p_sng q) (tt, p_none); s_var x) ]] 
    | q [[ s_loop x (s_recv (tt, p_none); s_var x) ]] ]
    ===> [ { ps } [[ s_skip ]] | q [[ s_skip ]] ].
Proof.
  intros.
  eapply rewrite_trans; 
    [ eapply rewrite_unroll_loop with (i := 0); simpl | idtac]. 
  reflexivity.
  reflexivity.
  simpl.
  eapply rewrite_trans; 
    [ eapply rewrite_unroll_loop with (i := 1); simpl | idtac]. 
  reflexivity.
  reflexivity.
  simpl.
  reduce_pair 0 1.
  eapply rewrite_trans.
  eapply rewrite_elim_unroll with (i := 0).
  cbv. reflexivity.
  cbv. reflexivity.
  cbv. reflexivity.
  cbv.
  apply rewrite_pair with (i1 := 0) (i2 := 1).
  reflexivity.
  reflexivity.