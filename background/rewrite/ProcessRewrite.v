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
  Inductive Var :=
    | X : nat -> Var.
  Inductive MuVar :=
    | L : nat -> MuVar.
  Definition eq_dec_pid := PeanoNat.Nat.eq_dec. 

  Inductive PidClass : Type :=
  | p_none : PidClass
  | p_sng  : pid -> PidClass
  | p_var  : Var -> PidClass
  | p_set  : Var -> PidClass.
  
  Definition eqb_var (xs ys : Var) : bool :=
    match (xs, ys) with
      | (X xs, X ys) => Nat.eqb xs ys
    end.
  
  Definition eqb_pidclass (p q : PidClass) :=
    match p, q with
      | p_none, p_none => true
      | p_sng p', p_sng q' => Nat.eqb p' q'
      | p_set ps, p_set qs => eqb_var ps qs
      | p_var x, p_var y => eqb_var x y 
      | _,_ => false
    end.
        
  Definition eq_dec_pidclass : forall (p q : PidClass), {p=q}+{p<>q}.
  Proof. repeat decide equality. Qed.
  
  (* Lemma eqb_pidclass_eq :  *)
  (*   forall (p q : PidClass), *)
  (*     eqb_pidclass p q = true <-> p = q. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct (eq_dec_pidclass p q). subst. *)
  (*   split; intros. reflexivity.  *)
  (*   destruct q. reflexivity. simpl. induction p; auto. *)
    
  (*   simpl. destruct s. unfold eqb_setvar. induction n; auto. *)
  (*   destruct p; destruct q; split; intros; try inversion H; try congruence. *)
  (*   apply PeanoNat.Nat.eqb_eq in H1. subst. reflexivity. *)
  (*   destruct s; destruct s0. *)
  (*   apply PeanoNat.Nat.eqb_eq in H1. subst. reflexivity. *)
  (* Qed.  *)

  Definition M := (T * PidClass)%type.

  Definition subst_pid_m (p1 : PidClass) (p2 : PidClass) (m : M) :=
    match (p1, m) with
      | (p_sng pid1, (t, p_sng pid2)) => 
        if Nat.eqb pid1 pid2 then
          (t, p2)
          else m
      | _ =>  m
    end.
    
  Inductive Stmt : Type :=
  | s_skip  : Stmt
  | s_send  : PidClass -> M -> Stmt
  | s_recv  : M -> Stmt
  | s_recv_l: list (M * Stmt) -> Stmt
  | s_recv_x: (T * Var) -> Stmt -> Stmt
  (* | s_int_ch : Stmt -> Stmt -> Stmt *)
  (* | s_ext_ch : Stmt -> Stmt -> Stmt *)
  | s_seq   : Stmt -> Stmt -> Stmt
  | s_iter  : Var -> Stmt -> Stmt
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
 
  Definition set_in_msg (xs : Var) (m : M) :=
    match m with
      | (_, p_set xs') => xs = xs'
      | _ => False
    end.

  Fixpoint set_in (xs : Var) (s : Stmt) :=
    match s with
      (* | s_int_ch s t => set_in xs s \/ set_in xs t *)
      (* | s_ext_ch s t => set_in xs s \/ set_in xs t *)
      | s_recv_l ss => fold_left (fun i s => i \/ 
                                             set_in_msg xs (fst s) \/ 
                                             set_in xs (snd s)) ss False
      (* | s_bind _ t => set_in xs t *)
      | s_seq t u => set_in xs t \/ set_in xs u
      | s_send (p_set xs') m => xs = xs' \/ set_in_msg xs m
      | s_recv m => set_in_msg xs m
      | s_recv_x (t,x') u => x' = xs \/ set_in xs u
      | s_iter _ t => set_in xs t
      | s_loop _ t => set_in xs t
      | s_loop_body _ t => set_in xs t
      | s_loop_end _ t => set_in xs t
      | _ => True
    end.
  
  Axiom measure : Var -> nat.

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
    | stmt_unfold_exit :
        forall (s : Stmt) (X : MuVar),
          EqStmt 
            (s_loop X s)
            (s_seq (s_loop_end X s) (s_loop X s))
    | stmt_fold_loop :
        forall (s : Stmt) (X : MuVar),
          EqStmt 
            (s_seq (s_loop_body X (s_var X)) (s_loop X s))
            (s_loop X s)
    | stmt_exit_loop :
        forall (s : Stmt) (X : MuVar),
          EqStmt 
            (s_seq (s_loop_end X s_skip) (s_loop X s))
            s_skip
    | stmt_set : 
        forall (s : Stmt) (xs xs' : Var),
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
  | Mult : Var -> Context
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
      | s_loop_end x t  => s_loop_end x (rest_stmt t)
      (* | s_loop x t  => s_loop x (rest_stmt t) *)
      | _           => s_skip
    end.

  Definition seq s1 s2 :=
    match s2 with 
      | s_skip => s1
      | _ => s_seq s1 s2
    end.
  
  (* Definition squish s := *)
  (*   match s with *)
  (*     | s_iter _ s_skip => s_skip  *)
  (*     | s_seq s1 s2 => seq s1 s2 *)
  (*   end. *)
  
  Fixpoint update_head_stmt h s :=
    match s with
      | s_seq s' t       => s_seq (update_head_stmt h s') t
      | s_iter xs s'     => 
        match update_head_stmt h s' with 
          | s_skip => s_skip 
          | s''    => s_iter xs s''
        end
      | s_loop_body x s' => s_loop_body x (update_head_stmt h s')
      | s_loop_end x s'  => s_loop_end x (update_head_stmt h s')
      | s'               => h
    end.
  
  Definition get_pid  (x : PidClass * (Stmt * list Context)) := fst x.
  Definition get_stmt (x : PidClass * (Stmt * list Context)) := fst (snd x).
  Definition get_ctx  (x : PidClass * (Stmt * list Context)) := snd (snd x).
  
  Definition eq_dec_m : forall m1 m2 : M, {m1=m2}+{m1<>m2}.
  Proof. repeat decide equality. Qed.
  
  Definition subst_pid p q p' :=
    if eqb_pidclass p p' then q else p'.
    (* match (p, p') with *)
    (*   | (p_sng p, p_sng pid') => if eq_dec_pid p pid' then q else p' *)
    (*   | _ => p' *)
    (* end. *)
  
  Fixpoint subst_stmt p q s :=
    match s with
      | s_skip => s_skip
      | s_send p' m => s_send (subst_pid p q p') (subst_pid_m p q m)
      | s_recv m => s_recv (subst_pid_m p q m)
      | s_seq s' t' => s_seq (subst_stmt p q s') (subst_stmt p q t')
      | s_loop_body x s' => s_loop_body x (subst_stmt p q s')
      | s_loop_end x s' => s_loop_end x (subst_stmt p q s')
      | _ => s
    end.
  
  Fixpoint inst_stmt (x : Var) (c : list PidClass) (s : Stmt) :=
    match s with
      | s_recv_x (t,x') s' =>
        if eqb_var x x' then
          s_recv_l (map (fun p => ((t,p), subst_stmt (p_var x) p s')) c)
        else
          s_recv_x (t, x') (inst_stmt x c s')
      | s_seq t u => s_seq (inst_stmt x c t) (inst_stmt x c u)
      | s_iter xs s => s_iter xs (inst_stmt x c s)
      | s_loop_body y s => s_loop_body y (inst_stmt x c s)
      | s_loop_end y s => s_loop_end y (inst_stmt x c s)
      (* | s_loop y s => s_loop y (inst_stmt x c s) *)
      | _ => s
    end.
  
  (* Definition elim ps qs := *)
  (*   match (get_stmt ps, get_stmt qs) with *)
  (*     | (s_send q m, s_recv m') =>  *)
  (*       if (eq_dec_m m m') then eqb_pidclass q (get_pid qs) else false *)
  (*     | (s_recv m', s_send p m) =>  *)
  (*       if (eq_dec_m m m') then eqb_pidclass p (get_pid ps) else false *)
  (*     | _ => false *)
  (*   end. *)
  
  Definition Elim ps qt :=
    match (get_stmt ps, get_stmt qt) with
      | (s_send q m, s_recv m') => 
        q = get_pid qt /\ m = m'
      | (s_recv m, s_send p m') => p = get_pid ps /\ m = m'
      | _ => False
    end.
    
  Definition MatchCtxt ps qt :=
    match (get_pid ps, get_pid qt, get_ctx ps, get_ctx qt) with
      | (p_sng p', p_sng q', c1, c2) => c1 = c2
      | (p_set ps, p_sng q', [], [Mult ps']) => ps = ps'
      | (p_sng p', p_set qs, [Mult qs'], []) => qs = qs'
      | (p_set ps, p_sng q, [], [Loop x]) => True
      | (p_sng p, p_set qs, [Loop x], []) => True
      | (_, _, [Loop x], [Loop x']) => x = x'
      | (_, _, [Loop x], [Mult qs]) => True
      | (_, _, [Mult qs],[Loop x]) => True
      | _ => False
    end.
  
  Inductive Event :=
    | tr_skip   : Event
    | tr_send   : PidClass -> PidClass -> T -> Event
    | tr_choose : PidClass -> PidClass -> list (M * Stmt) -> Event
    | tr_inst   : PidClass -> PidClass -> Event.
  
  Definition event_of s1 s2 :=
    match s1, s2 with
      | (p1, s_send _ (t,_)), (p2, s_recv _) => tr_send p1 p2 t 
      | (p2, s_recv (t,_)), (p1, s_send _ _) => tr_send p1 p2 t 
      | _, _ => tr_skip
    end.
  
  Definition stitch s1 s2 :=
    match s1, s2 with
      | s_skip, _ => s2
      | _, s_skip => s_skip
      | _, _ => s_seq s1 s2
    end.
  
  Definition dom (c : Config) := map fst c.
        
  Inductive RewriteRel : list Event -> Config -> Config -> Prop :=
  | rewrite_refl : 
      forall (c : Config), 
        RewriteRel [tr_skip] c c

  | rewrite_trans :
      forall (c1 c2 c3 : Config) (t1 t2 : list Event),
        RewriteRel t1 c1 c2 -> RewriteRel t2 c2 c3 ->
        RewriteRel (t1 ++ t2) c1 c3
                 
  | rewrite_eq_stmt :
      forall (c : Config) (i : nat) (p : PidClass) (s t : Stmt),
        nth_config c i = Some (p, s) ->
        EqStmt s t ->
        RewriteRel [] c (update_nth c i (p, t))
                   
  | rewrite_bind :
    forall (c : Config) (i : nat) (p : PidClass) (x : Var) (s s' : Stmt)
           (t : T),
      nth_config c i = Some (p, s) ->
      fst (head_stmt s) = s_recv_x (t, x) s' ->
      RewriteRel [] c (update_nth c i (p, inst_stmt x (dom c) s))

  | rewrite_choice :
    forall (c : Config) (i j k : nat) (p q : PidClass) (s t : Stmt) (mu : M * Stmt)
           (ts : list (M * Stmt)),
      nth_config c i = Some (p, s) ->
      nth_config c j = Some (q, t) ->
      fst (head_stmt t) = s_recv_l ts ->
      nth_error ts k = Some mu ->
      Elim (p, head_stmt s) (q, (s_recv (fst mu), snd (head_stmt t))) ->
      MatchCtxt (p, head_stmt s) (q, head_stmt t) ->
      RewriteRel [tr_choose p q ts] c 
                 (update_nth (update_nth c j (q, update_head_stmt (snd mu) t))
                                           i (p, rest_stmt s))

  | rewrite_pair :
    forall (c : Config) (i1 i2 : nat) (p1 p2 : PidClass) (s1 s2 : Stmt),
      nth_config c i1 = Some (p1, s1) -> 
      nth_config c i2 = Some (p2, s2) ->
      Elim (p1, head_stmt s1) (p2, head_stmt s2) ->
      MatchCtxt (p1, head_stmt s1)  (p2, head_stmt s2) ->
      RewriteRel [event_of (p1, fst (head_stmt s1)) (p2, fst (head_stmt s2))]
        c (update_nth (update_nth c i1 (p1, rest_stmt s1)) i2 (p2, rest_stmt s2)).
  
  Definition Clock := PidClass -> nat.
  Definition ClockV := PidClass -> Clock.

  Definition inc_my_clock old_cs me :=
    fun i => if eq_dec_pidclass i me then
               (fun them => if eq_dec_pidclass them me then 
                              old_cs me me + 1 
                            else 
                              old_cs me them)
             else
               old_cs i.
  
  Definition merge_clocks (cs : ClockV) (them me : PidClass) :=
    fun i => if eq_dec_pidclass i me then
               (fun c => PeanoNat.Nat.max
                           (cs them c) (cs me c))
             else
               cs i.

  Fixpoint run_clock (cs : ClockV) (es : list Event) :=
    match es with
      | nil => nil
      | tr_send a b t :: es' => 
        (tr_send a b t, cs) ::
        run_clock (merge_clocks (inc_my_clock (inc_my_clock cs a) b) a b) es'
      | tr_choose a b ss :: es' => 
        (tr_choose a b ss, cs) ::
        run_clock (merge_clocks (inc_my_clock (inc_my_clock cs a) b) a b) es'
      | _ :: es' => 
        run_clock cs es'
    end.
  
  Definition ClocksLt (cs cs' : ClockV) (i j : PidClass) :=
    (forall x, cs i x <= cs' j x) /\ 
    (exists x, cs i (p_sng x) < cs' j (p_sng x)).
  
  Definition Overlap (x y : list M) := 
    exists i j, In i x /\ In i y /\ ~ In j x \/ ~ In j y.
  
  Definition SameProcs (p1 p2 : PidClass) :=
    match p1, p2 with
    | p_sng a, p_sng b   => a  = b
    | p_set xs, p_set ys => xs = ys
    | _, _ => True
    end.
  
  Definition DistinctProcs (p1 p2 : PidClass) :=
    match p1, p2 with
    | p_sng a, p_sng b => a <> b
    | p_set xs, p_set ys => xs <> ys
    | _, _ => True
    end.
  
  Definition NoRaces (e : (Event * ClockV)) (es : list (Event * ClockV)) :=
    Forall (fun e' => 
              match fst e, fst e' with
                | tr_choose a b s, tr_choose a' b' s' =>
                  DistinctProcs a a' /\ SameProcs b b' /\
                  map snd s <> map snd s' /\
                  Overlap (map fst s) (map fst s')
                  -> ClocksLt (snd e) (snd e') a a'
                | _,_ => True
              end) es.
 
  (* Definition find_races (e : Event) (es : list (Event * ClockV)) := *)
  (*   fst (partition (fun x =>  *)
  (*                     match e, fst x with *)
  (*                       | tr_choose a b s, tr_choose a' b' s' => *)
  (*                         a <> a' /\ b = b' /\ *)
  (*                         map snd s <> map snd s' /\ *)
  (*                         Overlap (map fst s) (map fst s') *)
  (*                    | _, _ => false *)
  (*                  end) es). *)
  
  (* Definition CheckE ec1 ec2 := *)
  (*   match fst ec1, fst ec2 with *)
  (*     | tr_inst a _, tr_inst b _ => ClocksLt (snd ec1) (snd ec2) a b *)
  (*     | _,_ => True *)
  (*   end. *)
   
  Fixpoint Causal' (es : list (Event * ClockV)) :=
    match es with
      | [] => True
      | ec :: es' => NoRaces ec es' /\ Causal' es'
      (* | ec :: es' => match find_races (fst ec) es' with *)
      (*                  | [] => Causal' es' *)
      (*                  | es => fold_left (fun p ec' => p /\ CheckE ec ec') es (Causal' es') *)
                     (* end *)
    end.
  
  Definition Causal t := Causal' (run_clock (fun _ _ => 0) t).
 
  (* Parameter t : T. *)

  (* Definition x :=  (run_clock (fun _ => fun _ => 0)  *)
  (*                 [tr_send (p_sng 0) (p_sng 2) t;  *)
  (*                   tr_send (p_sng 0) (p_sng 1) t;  *)
  (*                   tr_send (p_sng 2) (p_sng 1) t]) : list (Event * (PidClass -> PidClass -> nat))%type. *)
  
  (* Ltac simpl_clocks := *)
  (*   repeat (cbn; match goal with  *)
  (*     | |- context[eq_dec_pidclass ?x ?x] => destruct (eq_dec_pidclass x x); [ idtac | congruence ] *)
  (*     | |- context[eq_dec_pidclass ?x ?y] => destruct (eq_dec_pidclass x y); [ congruence | idtac ] *)
  (*     | |- context[eq_dec_pidclass ?x ?y] => destruct (eq_dec_pidclass x y)  *)
  (*     | |- context[merge_clocks] => unfold merge_clocks at 1 *)
  (*     | |- context[inc_my_clock] => unfold inc_my_clock at 1 *)
  (*   end); try solve [cbv; auto]. *)
  
  (* Goal (Causal x). *)
  (*   Proof.  *)
  (*     intros. *)
  (*     simpl. *)
  (*     destruct (eq_dec_T t t); [ idtac | congruence ]. *)
  (*     unfold ClocksLt. *)
  (*     repeat split. *)
  (*     intros. *)
  (*     simpl_clocks. *)
  (*     simpl_clocks. *)
  (*     eapply ex_intro. *)

  (* Goal match (tl (tl x)) with *)
  (*        | (_, f)::_ => f (p_sng 1) (p_sng 1) = 2 *)
  (*        | _ => True *)
  (*      end. *)
  (* Proof. simpl_clocks. Qed. *)
  
  (* Definition c1 := (inc_my_clock (inc_my_clock (fun _ _ => 0) (p_sng 0)) (p_sng 1)). *)
  (* Definition c2 := (inc_my_clock (inc_my_clock (fun _ _ => 0) (p_sng 1)) (p_sng 1)). *)
  
  (* Goal  *)
  (*   forall (i : PidClass), *)
  (*     c2 (p_sng 0) i <= c1 (p_sng 1) i. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold c1, c2. *)
  (*   simpl_clocks.  *)
  (* Qed. *)

(* Fixpoint first_st (f : Trace -> bool) (l : list Trace) := *)
(*   match l with *)
(*     | [] => ([], None) *)
(*     | h::t => if f h then *)
(*                 ([], Some h) *)
(*               else *)
(*                 match first_st f t with *)
(*                   | (l', xo) => (h :: l', xo) *)
(*                 end *)
(*   end. *)

(* Definition Linear' (t : Trace) (ts : list Trace) : Prop := *)
(*   match t with *)
(*     | tr_send a b t => *)
(*       match first_st (fun x => match x with *)
(*                                  | tr_send a' b' t' => *)
(*                                    andb (negb (eqb_pidclass a a')) *)
(*                                         (andb (eqb_pidclass b b') *)
(*                                               (if eq_dec_T t t' then true else false)) *)
(*                                  | _ => false *)
(*                                end) ts with *)
(*         | (_, None) => True *)
(*         | (ls, Some t') => True *)
(*       end *)
(*     | _ => True *)
(*   end. *)

(* Inductive prefix : Trace -> Trace -> list Trace -> Prop := *)
(* | prefix_in : *)
(*     forall t1 t2 ts ts', *)
(*       In t1 ts -> In t2 ts' -> prefix t1 t2 (ts ++ ts'). *)

(* Inductive prefix_II_IO_chain : Trace -> Trace -> list Trace -> Prop := *)
(* | IO_end :  *)
(*     forall (p q : PidClass) (t : T) *)
(*            prefix *)
      
(* | II_IO_chain : *)
(*     forall t1 t2  *)


(* Fixpoint Linear (t : list Trace) : Prop := *)
(*   match t with *)
(*     | [] => True *)
(*     | t::ts => Linear' t ts /\ Linear ts *)
(*   end. *)
  

(* Axiom linear_skip_1 : forall (t : list Trace), *)
(*                       Linear (tr_skip::t) <-> Linear t. *)
(* Axiom linear_skip_2 : forall (t : list Trace), *)
(*                       Linear (t ++ [tr_skip]) <-> Linear t. *)

Fixpoint seq_stmts ss :=
  match ss with
    | []%list => s_skip
    | s::nil => s
    | (s::ss) => s_seq s (seq_stmts ss)
  end.
End Process.
Hint Constructors RewriteRel : rewrite.

Local Close Scope list.
Delimit Scope config_scope with config.
(* Notation "[ x ]" := (cons x nil) : config. *)
(* Notation "[ x | .. | y ]" := (cons x .. (cons y nil) ..) : config. *)

Delimit Scope stmt_scope with stmt.

Notation "[[ S1 ]]" := (S1) : stmt.
Notation "[[ S1 ; .. ; S2 ]]" := (seq S1 .. (seq S2 s_skip) ..) : stmt.
Notation "P @ S" := (p_sng P, S) (at level 80).
Notation "{ P } @ S " := (p_set P, S) (at level 80).
Notation "C1 ===> C2 + T " := (RewriteRel T C1 C2) (at level 95).
Notation "C1 ===> C2 " := (exists T, RewriteRel T C1 C2 /\ Causal T) (at level 95).
Notation "X ~ recv( T ) S" := (s_recv_x (T, X) S) (at level 60).