Require Export ProcessRewrite.
Require Export RewriteTactics.
Import ListNotations.

Open Scope config.
Open Scope stmt.
Open Scope list.

Inductive Message : Set :=
  | Integer : Message.
Definition eq_dec_Message : forall (m1 m2 : Message), {m1=m2}+{m1<>m2}.
Proof. decide equality. Qed.

Example MasterSlave :
  forall (p : pid) (xs qs : Var),
    measure xs = measure qs ->
    [ p    @ [[ s_iter xs (s_recv (Integer, p_none)) ]]
    ; {qs} @ [[ s_send (p_sng p) (Integer, p_none) ]]
    ] 
    ===> [ p @ [[ s_skip ]] ; {qs} @ [[ s_skip ]] ].
Proof.
  begin.
  rewrite_eq_stmt 0.
  apply stmt_set; auto.
  reduce_pair 0 1.
  skip.
  trust_me_its_causal.
Qed.