Require Export ProcessRewrite.
Require Export RewriteTactics.

Inductive Message :=
  | Integer.

Example MasterSlave :
  forall (p : pid) (xs : SetVar) (qs : SetVar),
    measure xs = measure qs ->
    [ p    [[ s_iter xs (s_recv (Integer, p_none)) ]]
    | {qs} [[ s_send (p_sng p) (Integer, p_none) ]]
    ] 
      ===> 
    [ p    [[ s_skip ]]
    | {qs} [[ s_skip ]]
    ].
Proof.
  intros.
  rewrite_eq_stmt 0.
  apply stmt_set; auto.
  reduce_pair 0 1.
  skip.
Qed.