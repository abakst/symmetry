Require Export ProcessRewrite.
Require Export RewriteTactics.
Import ListNotations.

Inductive PingPong :=
| Ping : PingPong
| Pong : PingPong.

Open Scope config.
Open Scope stmt.
Open Scope list.

Example PingPong_many :
  forall (q : nat) (x ps : Var),
     ( [ { ps } @ [[ s_send (p_sng q) (tt, p_set ps); 
                     s_recv_x (tt,x) s_skip ]]
       ; q      @ [[ s_iter ps
                   (s_recv_x (tt,x) (s_send (p_var x) (tt, p_sng q))) ]]
      ] ===>
      [ { ps } @ s_skip ; q @ s_skip ]).
Proof.
  begin.
  inst_bind 1. 
  reduce_choice 0 1 0.
  inst_bind 0.
  reduce_choice 1 0 1.
  skip.
  trust_me_its_causal.
Qed.