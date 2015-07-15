Require Export ProcessRewrite.
Require Export RewriteTactics.

Inductive PingPong :=
| Ping : PingPong
| Pong : PingPong.

Example PingPong_many :
  forall (q x : nat) (ps : SetVar),
    q <> x ->
    [ { ps } [[ s_send (p_sng q) (Ping, p_set ps); x ~ (s_recv (Pong, p_sng x)) ]]
    |   q  [[ s_iter ps
              (x ~ (s_recv (Ping, p_sng x); s_send (p_sng x) (Pong, p_sng q)))]] ]
    ===> [ { ps } [[ s_skip ]] | q [[ s_skip ]] ].
Proof.
  intros.
  inst_bind 1.
  reduce_pair 0 1.
  inst_bind 0.
  reduce_pair 0 1.
  skip.
Qed.