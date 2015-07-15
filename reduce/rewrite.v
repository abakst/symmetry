Require Export List.
Import ListNotations.
Require Export Setoid.
Require Export Morphisms.
Require Export SetoidTactics.
Require Import RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.

Section Process.
  Definition pid := nat.
  Context {T : Type}.
  Context {X : Type}. (** set vars **)
  Context {L : Type}. (** Loop Variables **)
  Definition eq_dec_pid := PeanoNat.Nat.eq_dec. 
  (* : forall (x y : pid), {x = y}+{x<>y}}. *)

  Inductive PidClass : Type :=
  | p_none : PidClass
  | p_sng  : pid -> PidClass
  | p_set  : X -> PidClass.
  
  (* Definition eq_dec_ *)

  Definition M := (T * PidClass)%type.
  Definition subst_pid_m (p1 : PidClass) (p2 : PidClass) (m : M) :=
    match (p1, m) with
      | (p_sng pid1, (t, p_sng pid2)) => 
        if eq_dec_pid pid1 pid2 then
          (t, p2)
          else m
      | _ =>  m
    end.
    
  Inductive Stmt : Type :=
  | s_skip  : Stmt
  | s_bind  : PidClass -> Stmt -> Stmt
  | s_send  : PidClass -> M -> Stmt
  | s_recv  : M -> Stmt
  | s_seq   : Stmt -> Stmt -> Stmt
  | s_iter  : X -> Stmt -> Stmt
  | s_loop  : L -> Stmt -> Stmt.
  
  Inductive Config  : Type := 
  | cfg_emp : Config
  | cfg_sng : PidClass -> Stmt -> Config
  | cfg_par : Config -> Config -> Config.

  Inductive EqConfig : Config -> Config -> Prop :=
  | cfg_refl : forall (c : Config),
    EqConfig c c
  | cfg_sym : forall (c d : Config),
    EqConfig c d -> EqConfig d c
  | cfg_trans : forall (c d e : Config),
    EqConfig c d -> EqConfig d e -> EqConfig c e
  | cfg_emp_unit : forall (c : Config),
    EqConfig c (cfg_par c cfg_emp)
  | cfg_comm  : forall (c d : Config),
    EqConfig (cfg_par c d) (cfg_par d c)
  | cfg_assoc : forall (c d e : Config), 
    EqConfig (cfg_par (cfg_par c d) e) (cfg_par c (cfg_par d e)).
  
  Instance EqConfig_equiv : Equivalence EqConfig := _.
  Proof.
    refine (Build_Equivalence _ _ _ _); hnf; intros.
    apply cfg_refl.
    eauto using cfg_sym.
    eauto using cfg_trans.
  Defined.
  
  Axiom Floobert : Proper (EqConfig ==> EqConfig ==> EqConfig) cfg_par.
  Instance FloobertI :Proper (EqConfig ==> EqConfig ==> EqConfig) cfg_par := Floobert.
  
  Axiom Foo : Proper (EqConfig ==> EqConfig ==> iff) EqConfig.
  Instance FooI : Proper (EqConfig ==> EqConfig ==> iff) EqConfig := Foo.
  
  Inductive EqStmt : Stmt -> Stmt -> Prop :=
    | stmt_refl : forall (s : Stmt), EqStmt s s 
    | stmt_sym : forall (s t : Stmt), 
      EqStmt s t -> EqStmt t s
    | stmt_trans : forall (s t u : Stmt), 
      EqStmt s t -> EqStmt t u -> EqStmt s u
    | stmt_skip1 : forall (s : Stmt),
      EqStmt s (s_seq s s_skip)
    | stmt_skip2 : forall (s : Stmt),
      EqStmt s (s_seq s_skip s).
  
  Instance EqStmt_equiv : Equivalence EqStmt := _.
  Proof.
    refine (Build_Equivalence _ _ _ _); hnf; intros.
    apply stmt_refl.
    eauto using stmt_sym.
    eauto using stmt_trans.
  Defined.
   
  Inductive Context :=
  | Mult : X -> Context
  | Loop : L -> Context.

  Fixpoint head_stmt' s stk :=
    match s with
      | s_seq s' _   => head_stmt' s' stk
      | s_iter xs s' => head_stmt' s' (Mult xs :: stk)
      | s_loop x  s' => head_stmt' s' (Loop x  :: stk)
      | s'           => (s',stk)
    end.
  Definition head_stmt s := head_stmt' s [].
  
  Fixpoint rest_stmt s :=
    match s with
      | s_seq s' t  => match rest_stmt s' with
                         | s_skip => t
                         | s''    => s''
                       end
      | s_iter xs t => match rest_stmt t with
                         | s_skip => s_skip
                         | t'     => s_iter xs t'
                       end
      | s_loop x t  => s_loop x (rest_stmt t)
      | _           => s_skip
    end.
  
  Definition get_pid  (x : PidClass * (Stmt * list Context)) := fst x.
  Definition get_stmt (x : PidClass * (Stmt * list Context)) := fst (snd x).
  Definition get_ctx  (x : PidClass * (Stmt * list Context)) := snd (snd x).
  
  Definition Elim ps qt :=
    match (get_stmt ps, get_stmt qt) with
      | (s_send p m, s_recv m') => 
        p = get_pid qt /\ m = m'
      | (s_recv m, s_send q m') => q = get_pid ps /\ m = m'
      | _ => False
    end.
  
  Definition MatchCtxt ps qt :=
    match (get_pid ps, get_pid qt, get_ctx ps, get_ctx qt) with
      | (p_sng p', p_sng q', c1, c2) => c1 = c2
      | (p_set ps, p_sng q', [], [Mult ps']) => ps = ps'
      | (p_sng p', p_set qs, [Mult qs'], []) => qs = qs'
      | _ => False
    end.
  
  Definition subst_pid p q p' :=
    match (p, p') with
      | (p_sng p, p_sng pid') => if eq_dec_pid p pid' then q else p'
      | _ => p'
    end.
  
  Fixpoint subst_stmt p q s :=
    match s with
      | s_skip => s_skip
      | s_send p' m => s_send (subst_pid p q p') (subst_pid_m p q m)
      | s_recv m => s_recv (subst_pid_m p q m)
      | s_seq s' t' => s_seq (subst_stmt p q s') (subst_stmt p q t')
      | _ => s
    end.
  
  Fixpoint inst_stmt (p q : PidClass) s :=
    match s with
      | s_seq t u => s_seq (inst_stmt p q t) (inst_stmt p q u)
      | s_iter xs s => s_iter xs (inst_stmt p q s)
      | s_loop x s => s_loop x (inst_stmt p q s)
      | s_bind x s => 
        match (x, p) with
          | (p_sng x', p_sng p') => 
            if eq_dec_pid x' p' then subst_stmt p q s else s
          | _ => s
        end
      | _ => s
    end.
        
  Inductive RewriteRel : Config -> Config -> Prop :=
  | rewrite_refl : forall (c : Config), RewriteRel c c
  | rewrite_comm : forall (c1 c2 : Config),
    RewriteRel (cfg_par c1 c2) (cfg_par c2 c1)
  | rewrite_ass : forall (c d e : Config),
    RewriteRel (cfg_par c (cfg_par d e)) (cfg_par (cfg_par c d) e)
  | rewrite_trans :
    forall (c1 c2 c3 : Config),
      RewriteRel c1 c2 -> RewriteRel c2 c3 ->
      RewriteRel c1 c3
  | rewrite_frame :
    forall (c1 c2 c3 : Config),
      RewriteRel c1 c2 ->
      RewriteRel (cfg_par c1 c3) (cfg_par c2 c3)
  | rewrite_bind :
    forall (p q r : PidClass) (s t : Stmt),
      fst (head_stmt s) = s_bind q t ->
      RewriteRel (cfg_sng p s) (cfg_sng p (inst_stmt q r s))
  | rewrite_pair_elim : 
    forall (p q : PidClass) (s t : Stmt),
      Elim (p, head_stmt s) (q, head_stmt t) ->
      MatchCtxt (p, head_stmt s) (q, head_stmt t) ->
      RewriteRel (cfg_par (cfg_sng p s) (cfg_sng q t))
                 (cfg_par (cfg_sng p (rest_stmt s)) (cfg_sng q (rest_stmt t))).

  Axiom RewriteConfigMorphism :
    Proper (EqConfig ==> EqConfig ==> iff) RewriteRel.
  Instance RewriteConfigMorphism_Proper : Proper (EqConfig ==> EqConfig ==> iff) RewriteRel := RewriteConfigMorphism.
  
  Hint Constructors RewriteRel : rewrite.
 
End Process.
  
  Ltac frame_to_pair :=
    let t := match goal with
      | |- @RewriteRel _ _ _ _ (cfg_sng _ _) => fail
      | |- @RewriteRel _ _ _ _ (cfg_par (cfg_sng _ _) (cfg_sng _ _) ) => idtac
      | |- _ => eapply rewrite_trans; [apply rewrite_frame | cbv ]
    end in repeat t.
  
  Ltac reduce_top_pair :=
    frame_to_pair;
    eapply rewrite_trans; first [eapply rewrite_pair_elim; cbv; eauto; apply rewrite_refl; cbv | apply rewrite_refl; cbv | cbv].
  
  Ltac cycle_top :=
    setoid_rewrite cfg_assoc;
      setoid_rewrite cfg_comm.
  
  
  Inductive PingPong :=
  | Ping : PingPong
  | Pong : PingPong.

  Ltac rewrite_comm :=
    eapply rewrite_trans; [ apply rewrite_comm | idtac ].
  Ltac rewrite_assoc :=
    eapply rewrite_trans; [ apply rewrite_ass | idtac ].
  
  (* Definition eq_dec_pid := PeanoNat.Nat.eq_dec. *)
  
  Notation "P1 | P2" := (cfg_par P1 P2) (at level 90, left associativity).
  Notation "P1 ; P2" := (s_seq P1 P2) (at level 90, left associativity).
  Notation "P [[ S ]]" := (cfg_sng (p_sng P) S) (at level 80).
  Notation "{ P } [[ S ]]" := (cfg_sng (p_set P) S) (at level 80).
  Notation "C1 ===>N C2" := (RewriteRel (X:= nat) (L := nat) C1 C2) (at level 95).
  Notation "C1 ===> C2" := (RewriteRel (X:= nat) (L := nat) C1 C2) (at level 95).
  Notation " X ~ S" := (s_bind (p_sng X) S) (at level 60).
  
  Ltac next := rewrite_comm; rewrite_assoc.

  Example SimpleProtocol :
    forall (p q r : nat),
     RewriteRel (X := nat) (L := nat)
     (p [[ s_send (p_sng q) (tt, p_none) ]]
    | q [[ s_recv (tt, p_none); s_send (p_sng r) (tt, p_none) ]]
    | r [[ s_recv (tt, p_none) ]] )
     (p [[ s_skip ]] | q [[ s_skip ]] | r [[ s_skip ]]).
  Proof.
    intros.
    reduce_top_pair.
    next. next.
    reduce_top_pair.
    next.
    apply rewrite_refl.
  Qed.

  Example SimpleProtocol2 :
    forall (ps : nat) (q : nat),
     RewriteRel (X := nat) (L := nat)
      ({ ps } [[ s_recv (tt, p_none) ]] | q [[ s_iter ps (s_send (p_set ps) (tt, p_none)) ]] )
      ({ ps } [[ s_skip ]] | q [[ s_skip ]]).
  Proof.
    intros.
    reduce_top_pair.
  Qed.

  Ltac frame_to_top :=
    let t := match goal with
               | |- @RewriteRel _ _ _ _ (cfg_sng _ _) => idtac
               | _ => eapply rewrite_trans; [apply rewrite_frame | cbv ]
             end in repeat t.

  Ltac expand_subst :=
    simpl inst_stmt; simpl subst_stmt; unfold subst_pid_m, subst_pid;
      repeat match goal with 
               | |- context[eq_dec_pid ?x ?x] =>
                 destruct (eq_dec_pid x x); [ idtac | congruence]
               | |- context[eq_dec_pid ?x ?y] =>
                 destruct (eq_dec_pid x y); [ congruence | idtac]
             end.
  
  Ltac rewrite_top x :=
    frame_to_top;
    first [ eapply rewrite_bind with (r := x);
            reflexivity
          | try reflexivity 
          ]; expand_subst.
  
  Example SimpleProtocol3 : 
    forall (p q x : nat),
     RewriteRel (X := nat) (L := nat)
      (p [[ s_bind (p_sng x) (s_recv (tt, p_none)) ]]
      |q [[ s_send (p_sng p) (tt, p_none) ]])
      (p [[ s_skip ]] | q [[ s_skip ]]).
  Proof.
    intros.
    rewrite_top (p_sng (X := nat) x).
    reduce_top_pair.
  Qed.
  
  Example PingPong_single :
    forall (p q x : nat),
      p <> x -> p <> q -> q <> x ->
      p [[ s_bind (p_sng x) ((s_recv (Ping, p_sng x)); s_send (p_sng x) (Pong, p_sng p)) ]]
    | q [[ s_send (p_sng p) (Ping, p_sng q); s_recv (Pong, p_sng p) ]] ===>
      p [[ s_skip ]] | q [[ s_skip ]].
  Proof.
    intros.
    rewrite_top (p_sng (X := nat) q).
    reduce_top_pair.
    reduce_top_pair.
  Qed.
  
  Example PingPong_many :
    forall (q x : nat) (ps : nat),
      q <> x ->
      { ps } [[ s_send (p_sng q) (Ping, p_set ps); x ~ (s_recv (Pong, p_sng x)) ]]
      |   q  [[ s_iter ps 
                (x ~ (s_recv (Ping, p_sng x); s_send (p_sng x) (Pong, p_sng q)))]]
      ===> { ps } [[ s_skip ]] | q [[ s_skip ]].
  Proof.
    intros.
    rewrite_comm.
    rewrite_top (p_set (X := nat) ps).
    reduce_top_pair.
    rewrite_comm.
    rewrite_top (p_sng (X := nat) q).
    reduce_top_pair.
  Qed.

