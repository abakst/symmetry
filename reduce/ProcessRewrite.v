Require Export List.
Import ListNotations.
Require Export Setoid.
Require Export Morphisms.
Require Export SetoidTactics.
Require Import RelationClasses.
Require Export Coq.Structures.Orders.

Set Implicit Arguments.
Unset Strict Implicit.

Section Process.
  Context {T : Type}.
  Context {eq_dec_T : forall (t1 t2 : T), {t1 = t2}+{t1 <> t2}}.
  Definition pid := nat.
  Inductive SetVar :=
    | X : nat -> SetVar.
  Inductive MuVar :=
    | L : nat -> MuVar.
  Definition eq_dec_pid := PeanoNat.Nat.eq_dec. 

  Inductive PidClass : Type :=
  | p_none : PidClass
  | p_sng  : pid -> PidClass
  | p_set  : SetVar -> PidClass.
  
  Definition eqb_setvar (xs ys : SetVar) : bool :=
    match (xs, ys) with
      | (X xs, X ys) => Nat.eqb xs ys
    end.
  
  Definition eqb_pidclass (p q : PidClass) :=
    match p, q with
      | p_none, p_none => true
      | p_sng p', p_sng q' => Nat.eqb p' q'
      | p_set ps, p_set qs => eqb_setvar ps qs
      | _,_ => false
    end.
        
  Definition eq_dec_pidclass : forall (p q : PidClass), {p=q}+{p<>q}.
  Proof. repeat decide equality. Qed.
  
  Lemma eqb_pidclass_eq : 
    forall (p q : PidClass),
      eqb_pidclass p q = true <-> p = q.
  Proof.
    intros.
    destruct (eq_dec_pidclass p q). subst.
    split; intros. reflexivity. 
    destruct q. reflexivity. simpl. induction p; auto.
    simpl. destruct s. unfold eqb_setvar. induction n; auto.
    destruct p; destruct q; split; intros; try inversion H; try congruence.
    apply PeanoNat.Nat.eqb_eq in H1. subst. reflexivity.
    destruct s; destruct s0.
    apply PeanoNat.Nat.eqb_eq in H1. subst. reflexivity.
  Qed. 

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
  | s_recv_l: PidClass -> list (M * Stmt) -> Stmt
  | s_seq   : Stmt -> Stmt -> Stmt
  | s_iter  : SetVar -> Stmt -> Stmt
  | s_loop  : MuVar -> Stmt -> Stmt
  | s_var   : MuVar -> Stmt
  (* These statements below never appear in original programs *)
  | s_loop_body : MuVar -> Stmt -> Stmt
  | s_loop_end  : MuVar -> Stmt -> Stmt.

  
  Definition Process := (PidClass * Stmt)%type.
  Definition Config := list Process.
  
  Definition nth_config (c : Config) (n : nat) := nth_error c n.
  Fixpoint update_nth (c : Config) (n : nat) (ps : PidClass * Stmt) := 
    match (n, c) with
      | (O, _::cs) => ps::cs
      | (_, [])    => c
      | (S n, ps'::cs') => ps' :: update_nth cs' n ps
    end.
  
  Fixpoint set_in (xs : SetVar) (s : Stmt) :=
    match s with
      | s_int_ch s t => set_in xs s \/ set_in xs t
      | s_ext_ch s t => set_in xs s \/ set_in xs t
      | s_bind _ t => set_in xs t
      | s_seq t u => set_in xs t \/ set_in xs u
      | s_send (p_set xs') (_, p_set xs'') => xs = xs' \/ xs = xs''
      | s_recv (_, p_set xs') => xs = xs'
      | s_iter _ t => set_in xs t
      | s_loop _ t => set_in xs t
      | s_loop_body _ t => set_in xs t
      | s_loop_end _ t => set_in xs t
      | _ => False
    end.
  
  Axiom measure : SetVar -> nat.

  Inductive EqStmt : Stmt -> Stmt -> Prop :=
    | stmt_refl : 
        forall (s : Stmt), EqStmt s s 
    | stmt_sym : 
        forall (s t : Stmt), 
      EqStmt s t -> EqStmt t s
    | stmt_trans : 
        forall (s t u : Stmt), 
      EqStmt s t -> EqStmt t u -> EqStmt s u
    | stmt_skip1 : 
        forall (s : Stmt),
      EqStmt s (s_seq s s_skip)
    | stmt_skip2 : 
        forall (s : Stmt),
      EqStmt s (s_seq s_skip s)
    | stmt_seq :
        forall (s t s' t' : Stmt),
          EqStmt s s' -> EqStmt t t' -> EqStmt (s_seq s t) (s_seq s' t')
    | stmt_unfold_loop :
        forall (s : Stmt) (X : MuVar),
          EqStmt 
            (s_loop X s)
            (s_seq (s_loop_body X s) (s_loop X s))
    | stmt_fold_loop :
        forall (s : Stmt) (X : MuVar),
          EqStmt 
            (s_seq (s_loop_body X (s_var X)) (s_loop X s))
            (s_loop X s)
    | stmt_set : 
        forall (s : Stmt) (xs xs' : SetVar),
          ~ set_in xs s -> EqStmt (s_iter xs s) (s_iter xs' s).
  
  Hint Constructors EqStmt : eqstmt.
  
  Instance EqStmt_equiv : Equivalence EqStmt := _.
  Proof.
    refine (Build_Equivalence _ _ _ _); hnf; intros.
    apply stmt_refl.
    eauto using stmt_sym.
    eauto using stmt_trans.
  Defined.
  
  Instance proper_eq_seq : Proper (EqStmt ==> EqStmt ==> EqStmt) s_seq.
  Proof.
    repeat (hnf; intros).
    apply stmt_seq; assumption.
  Qed.
   
  Inductive Context :=
  | Mult : SetVar -> Context
  | Loop : MuVar -> Context.

  Fixpoint head_stmt' s stk :=
    match s with
      | s_seq s' _       => head_stmt' s' stk
      | s_iter xs s'     => head_stmt' s' (Mult xs :: stk)
      | s_loop_body x s' => head_stmt' s' (Loop x  :: stk)
      | s_loop_end x s'  => head_stmt' s' stk
      | s'               => (s',stk)
    end.
  
  Definition head_stmt s := head_stmt' s [].
  
  Fixpoint rest_stmt s :=
    match s with
      | s_seq s' t  => match rest_stmt s' with
                         | s_skip => t
                         | s''    => s_seq s'' t
                       end
      | s_iter xs t => match rest_stmt t with
                         | s_skip => s_skip
                         | t'     => s_iter xs t'
                       end
      | s_loop_body x t => s_loop_body x (rest_stmt t)
      (* | s_loop x t  => s_loop x (rest_stmt t) *)
      | _           => s_skip
    end.
  
  Fixpoint update_head_stmt h s :=
    match s with
      | s_seq s' t       => s_seq (update_head_stmt h s') t
      | s_iter xs s'     => s_iter xs (update_head_stmt h s')
      | s_loop_body x s' => s_loop_body x (update_head_stmt h s')
      | s_loop_end x s'  => s_loop_end x (update_head_stmt h s')
      | s'               => h
    end.
  
  Definition get_pid  (x : PidClass * (Stmt * list Context)) := fst x.
  Definition get_stmt (x : PidClass * (Stmt * list Context)) := fst (snd x).
  Definition get_ctx  (x : PidClass * (Stmt * list Context)) := snd (snd x).
  
  Definition eq_dec_m : forall m1 m2 : M, {m1=m2}+{m1<>m2}.
  Proof. repeat decide equality. Qed.
  
  Definition elim ps qs :=
    match (get_stmt ps, get_stmt qs) with
      | (s_send q m, s_recv m') => 
        if (eq_dec_m m m') then eqb_pidclass q (get_pid qs) else false
      | (s_recv m', s_send p m) => 
        if (eq_dec_m m m') then eqb_pidclass p (get_pid ps) else false
      | _ => false
    end.
  
  Definition Elim ps qt :=
    match (get_stmt ps, get_stmt qt) with
      | (s_send q m, s_recv m') => 
        q = get_pid qt /\ m = m'
      | (s_recv m, s_send p m') => p = get_pid ps /\ m = m'
      | _ => False
    end.
  
  Lemma elim_Elim :
    forall ps qs : PidClass * (Stmt * list Context),
      elim ps qs = true -> Elim ps qs.
  Proof.
    intros.
    destruct ps as [p [ps pc]]; destruct qs as [q [qs qc]]. 
    induction ps; destruct qs; try inversion H.
    unfold elim in H1.
    unfold get_stmt in H1.
    simpl in H1.
    destruct (eq_dec_m m m0). apply eqb_pidclass_eq in H1. subst.  
    cbv. auto. congruence.
    unfold elim in H. unfold get_stmt in H. simpl in H.
    destruct (eq_dec_m m0 m). apply eqb_pidclass_eq in H. subst.
    cbv. auto. congruence.
  Qed.
    
  Definition MatchCtxt ps qt :=
    match (get_pid ps, get_pid qt, get_ctx ps, get_ctx qt) with
      | (p_sng p', p_sng q', c1, c2) => c1 = c2
      | (p_set ps, p_sng q', [], [Mult ps']) => ps = ps'
      | (p_sng p', p_set qs, [Mult qs'], []) => qs = qs'
      | (_, _, [Loop x], [Loop x']) => x = x'
      | (_, _, [Loop x], [Mult qs]) => True
      | (_, _, [Mult qs],[Loop x]) => True
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
  | rewrite_refl : 
      forall (c : Config), 
        RewriteRel c c

  | rewrite_trans :
      forall (c1 c2 c3 : Config),
        RewriteRel c1 c2 -> RewriteRel c2 c3 ->
        RewriteRel c1 c3
                 
  | rewrite_eq_stmt :
      forall (c : Config) (i : nat) (p : PidClass) (s t : Stmt),
        nth_config c i = Some (p, s) ->
        EqStmt s t ->
        RewriteRel c (update_nth c i (p, t))

  | rewrite_bind :
    forall (c : Config) (i : nat) (p x q : PidClass) (s t : Stmt),
      nth_config c i = Some (p, s) ->
      fst (head_stmt s) = s_bind x t ->
      RewriteRel c (update_nth c i (p, inst_stmt x q s))
                 
  | rewrite_exit_loop :
    forall (c : Config) (i : nat) (p : PidClass) (s t : Stmt) (X : MuVar),
      nth_config c i = Some (p, s) ->
      fst (head_stmt s) = s_loop X t ->
      RewriteRel c (update_nth c i (p, s_loop_end X t))
                 
  | rewrite_ext_choice_l :
      forall (c : Config) (i : nat) (p : PidClass) (s t u : Stmt),
        nth_config c i = Some (p, s) ->
        fst (head_stmt s) = s_ext_ch t u ->
        RewriteRel c (update_nth c i (p, update_head_stmt t s))

  | rewrite_ext_choice_r :
      forall (c : Config) (i : nat) (p : PidClass) (s t u : Stmt),
        nth_config c i = Some (p, s) ->
        fst (head_stmt s) = s_ext_ch t u ->
        RewriteRel c (update_nth c i (p, update_head_stmt u s))

  | rewrite_pair :
    forall (c : Config) (i1 i2 : nat) (p1 p2 : PidClass) (s1 s2 : Stmt),
      nth_config c i1 = Some (p1, s1) -> 
      nth_config c i2 = Some (p2, s2) ->
      Elim (p1, head_stmt s1) (p2, head_stmt s2) ->
      MatchCtxt (p1, head_stmt s1) (p2, head_stmt s2) ->
      RewriteRel c (update_nth (update_nth c i1 (p1, rest_stmt s1)) i2 (p2, rest_stmt s2)).
End Process.

Hint Constructors RewriteRel : rewrite.

Notation "[ x ]" := (cons x nil).
Notation "[ x | .. | y ]" := (cons x .. (cons y nil) ..).
Notation "P1 ; P2" := (s_seq P1 P2) (at level 65, right associativity).
Notation "P [[ S ]]" := (p_sng P, S) (at level 80).
Notation "{ P } [[ S ]]" := (p_set P, S) (at level 80).
Notation "C1 ===> C2" := (RewriteRel C1 C2) (at level 95).
Notation "X ~ S" := (s_bind (p_sng X) S) (at level 60).
