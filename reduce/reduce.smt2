;; (set-option :smt.mbqi true)
(set-option :smt.macro-finder true)
(declare-sort U)
(declare-sort Pid)
(declare-sort PidClass)
(declare-sort PidSet)
(declare-sort Set)
(declare-sort Var)

(declare-fun Sing(Pid)     PidClass)
(declare-fun Multi(PidSet) PidClass)
(declare-fun In(PidSet) Pid)

(assert (forall ((p Pid) (q Pid))
                (=> (= (Sing p) (Sing q)) (= p q))))

(declare-fun size(Set) Int)
(declare-fun sizePids(PidSet) Int)

; Substitutions
(define-sort Subst () (Array Pid Pid))
  ; Empty
  (declare-const emptySubst Subst)
  (assert (forall ((p Pid)) (= (select emptySubst p) p)))
  ; Build 1 [p := q]
  (define-fun subst1 ((p Pid) (q Pid)) Subst
    (store emptySubst p q))

; Statements
(declare-sort Stmt)
  (declare-fun skip() Stmt)
  (declare-fun send(Pid U) Stmt)
  (declare-fun bind(Pid Stmt) Stmt)
  (declare-fun recv(U) Stmt)
  (declare-fun seq(Stmt Stmt) Stmt)
  (declare-fun foreach(PidSet Stmt) Stmt)
  (declare-fun iter(Set Stmt) Stmt)
  (declare-fun mu(Var Stmt) Stmt)
  (declare-fun var(Var) Stmt)
  (declare-fun offer(Stmt Stmt) Stmt)

  ;; "Helper" statements
  (declare-fun unroll-body(Var Stmt) Stmt)
  (declare-fun unroll-end(Var Stmt) Stmt)

; Substitution "type class"
(declare-fun apply-subst-u (Subst U) U)
(declare-fun apply-subst (Subst Stmt) Stmt)

; Substitution "instances"
(assert (forall ((s Subst)) (= (apply-subst s skip) skip)))
(assert (forall ((s Subst)
                 (p Pid)
                 (m U)) 
                (= (apply-subst s (send p m)) 
                   (send (select s p) (apply-subst-u s m)))))
(assert (forall ((s Subst)
                 (p Pid)
                 (t Stmt))
                (= (apply-subst s (bind p t)) (apply-subst (store s p p) t))))
(assert (forall ((s Subst)
                 (m U))
                (= (apply-subst s (recv m)) (recv (apply-subst-u s m)))))
(assert (forall ((s Subst)
                 (s1 Stmt)
                 (s2 Stmt))
                (= (apply-subst s (seq s1 s2)) (seq (apply-subst s s1)
                                                    (apply-subst s s2)))))
(assert (forall ((s Subst)
                 (t Stmt)
                 (x Var))
                (= (apply-subst s (mu x t)) (mu x (apply-subst s t)))))
(assert (forall ((s Subst) (x Var))
                (= (apply-subst s (var x)) (var x))))
(assert (forall ((s Subst) (t Stmt) (u Stmt))
                (= (apply-subst s (offer t u))
                   (offer (apply-subst s t) (apply-subst s u)))))

; Config is a collection of processes,
; i.e. PID => S
(define-sort Config () (Array PidClass Stmt))

(declare-fun Rewrite(Config Config) Bool)

(assert (forall ((s Config)) (Rewrite s s)))

(assert (forall ((c1 Config)
                 (c2 Config)
                 (c3 Config))
                (! (=> (Rewrite c1 c2)
                            (=> (Rewrite c2 c3)
                                     (Rewrite c1 c3)))
                   :pattern ((Rewrite c1 c2) (Rewrite c2 c3)))))


;; Triggers/Dummies
(declare-fun TC (Config) Bool)
(declare-fun TV (Pid) Bool)
(declare-fun TS (Stmt) Bool)
(declare-fun TP (PidClass) Bool)
(declare-fun OKSet(Set) Bool)
(declare-fun OKPidSet(PidSet) Bool)

; Congruence
(assert
 (forall ((x Var) (s Stmt))
         (= (seq (unroll-body x (seq (var x) skip)) s) s)))

(assert
 (forall ((x Var) (s Stmt))
         (= (seq (unroll-end x skip) s) s)))

(assert 
 (forall ((s Stmt) (t Stmt) (u Stmt))
         (! (= (seq s (seq t u)) (seq (seq s t) u))
            :pattern (TS (seq (seq s t) u)))))

(assert
 (forall ((s Stmt))
         (= s (seq skip s))))

(assert
 (forall ((s Stmt))
         (= s (seq s skip))))

(assert
 (forall ((xs Set))
         (= skip (iter xs skip)))) 

(assert
 (forall ((ps PidSet))
         (= skip (foreach ps skip))))

(assert
 (forall ((p Pid) (ps PidSet))
         (not (= (Sing p) (Multi ps)))))

; Rewrite Rules
(declare-const empty Config)

(define-fun is-proc ((c Config) (p PidClass) (s Stmt)) Bool
  (= (select c p) s))

(define-fun two-procs ((c Config) 
                       (p1 PidClass) (s1 Stmt) 
                       (p2 PidClass) (s2 Stmt)) Config
  (store (store c p1 s1) p2 s2))

(define-fun rewrite-1-rule ((c Config) 
                            (p1 PidClass)
                            (s1 Stmt)) Bool
  (and (Rewrite c (store c p1 s1))
       (TC (store c p1 s1))
       (TP p1)
       (TS s1)))

(define-fun rewrite-2-rule ((c Config) 
                            (p1 PidClass)
                            (s1 Stmt)
                            (p2 PidClass)
                            (s2 Stmt)) Bool
  (and (Rewrite c (two-procs c p1 s1 p2 s2))
       (TC (two-procs c p1 s1 p2 s2))
       (TP p1)
       (TP p2)
       (TS s1)
       (TS s2)))

(assert
 (forall ((p PidClass)) (= (select empty p) skip)))

;; (declare-fun m (Pid) U)

(assert
 (forall ((c Config) (d Config))
         (=>
          (and
           (Rewrite c d)
           (forall
            ((p PidClass)) (= (select d p) skip)))
          (Rewrite c empty))))

;; Binder instantiation
(assert
 (forall ((p PidClass)
          (q Pid)
          (r Pid)
          (c Config)
          (s Stmt))
         (! (=>
             (is-proc c p (bind q s))
             (rewrite-1-rule
              c
              p
              (apply-subst (subst1 q r) s)))
            :pattern
            ((TC c) (TP p) (TV r) (TS (bind q s))))))

;; Binder instantiation
(assert
 (forall ((p PidClass)
          (q Pid)
          (r Pid)
          (xs PidSet)
          (c Config)
          (s Stmt)
          (t Stmt))
         (! (=>
             (is-proc c p (seq (foreach xs (bind q s)) t))
             (rewrite-1-rule
              c
              p
              (seq (foreach xs (apply-subst (subst1 q r) s)) t)))
            :pattern
            ((TC c) (TP p) (TV r) (TS (seq (foreach xs (bind q s)) t))))))

;; Send/Recv
(assert
 (forall ((p1 Pid)
          (p2 Pid)
          (s1 Stmt)
          (s2 Stmt)
          (c1 Config)
          (m U))
         (! (=>
             (and
              ;; (not (= p1 p2))
              (is-proc c1 (Sing p1) (seq (send p2 m) s1))
              (is-proc c1 (Sing p2) (seq (recv m) s2)))
             (rewrite-2-rule
              c1
              (Sing p1) s1
              (Sing p2) s2))
         :pattern 
         ((TC c1)
          (TS (seq (send p2 m) s1))
          (TS (seq (recv m) s2))
          (TP (Sing p1))
          (TP (Sing p2))))))

;; Iteration?
(assert
 (forall ((p1 Pid)
          (p2 Pid)
          (xs Set)
          (ys Set)
          (s1 Stmt)
          (s2 Stmt)
          (t1 Stmt)
          (t2 Stmt)
          (c1 Config))
         (! (=>
             (and
              (= (size xs) (size ys))
              (not (= p1 p2))
              (is-proc c1 (Sing p1) (iter xs (seq s1 t1)))
              (is-proc c1 (Sing p2) (iter ys (seq s2 t2))))
              (let ((c2 (two-procs empty (Sing p1) s1
                                         (Sing p2) s2)))
                (=> (and (TC c2) (TS (seq s1 skip)) (TS (seq s2 skip)))
                    (Rewrite c2 empty)))
             (rewrite-2-rule
              c1
              (Sing p1) (iter xs t1)
              (Sing p2) (iter ys t2)))
         :pattern 
         ((OKSet xs)
          (OKSet ys)
          (TC c1)
          (TS (iter xs (seq s1 t1)))
          (TS (iter ys (seq s2 t2)))
          (TP (Sing p1))
          (TP (Sing p2))))))

;; Parallel/Sequential
(assert
 (forall ((p1 Pid)
          (ps PidSet)
          (s1 Stmt)
          (s2 Stmt)
          (s3 Stmt)
          (t1 Stmt)
          (t2 Stmt)
          (c1 Config))
         (! (let ((p1_proc (seq (foreach ps (seq s1 s2)) s3))
                   (p2_proc (seq t1 t2))
                   (ps_p (Sing (In ps))))
               (let ((c2 (two-procs empty (Sing p1) (seq s1 skip) ps_p (seq t1 skip))))
                 (=>
                  (and (is-proc c1 (Sing p1)  p1_proc)
                       (is-proc c1 (Multi ps) p2_proc)
                       (=> (and (TC c2) (TP ps_p) (TS (seq s1 skip)) (TS (seq t1 skip))
                                (not (= p1 (In ps))))
                           (Rewrite c2 empty)))
                  (rewrite-2-rule
                   c1
                   (Sing p1) (ite (= s2 skip) s3 (seq (foreach ps s2) s3))
                   (Multi ps) t2))))
            :pattern 
            ((OKPidSet ps)
             (TC c1)
             (TP (Sing p1))
             (TP (Multi ps))
             (TS (seq (foreach ps (seq s1 s2)) s3))
             (TS (seq t1 t2))))))

;; Parallel/Iteration rewrite
;; but this needs some syntactic checks...
(assert
 (forall ((xs Set)
          (ps PidSet)
          (s Stmt)
          (t Stmt)
          (q PidClass)
          (c Config))
         (! (=> (and (= (size xs) (sizePids ps))
                     (is-proc c q (seq (iter xs s) t)))
             (rewrite-1-rule c q (seq (foreach ps s) t)))
            :pattern
            ((OKPidSet ps)
             (OKSet xs)
             (TC c)
             (TP q)
             (TS (seq (iter xs s) t))))))

;;mu recursion can split into some number of iterations + an exit
(assert
 (forall ((p PidClass)
          (c Config)
          (x Var)
          (s Stmt)
          (t Stmt))
         (! (=> (is-proc c p (seq (mu x s) t))
                (rewrite-1-rule c p (seq (unroll-body x s)
                                    (seq (unroll-end x s) t))))
            :pattern
            ((TP p) (TC c) (TS (seq (mu x s) t))))))

;;Behavior of unroll-body with loops (1)
(assert
 (forall ((p PidClass)
          (c Config)
          (q Pid)
          (x Var)
          (xs Set)
          (s1 Stmt)
          (t1 Stmt)
          (u1 Stmt)
          (s2 Stmt)
          (t2 Stmt)
          (u2 Stmt))
         (! (let ((c2 (two-procs empty p (seq s1 skip) (Sing q) (seq s2 skip))))
          (=> (and (is-proc c p (seq (unroll-body x (seq s1 t1)) u1))
                   (is-proc c (Sing q) (seq (iter xs (seq s2 t2)) u2))
                   (=> (and (TC c2) (TS (seq s1 skip)) (TS (seq s2 skip))
                        (not (= p (Sing q))))
                       (Rewrite c2 empty)))
              (rewrite-2-rule c p       (seq (unroll-body x t1) u1)
                               (Sing q) (ite (= t2 skip) u2 (seq (iter xs t2) u2)))))
          :pattern
          ((TC c) 
           (TP p)
           (TP (Sing q))
           (TS (seq (unroll-body x (seq s1 t1)) u1))
           (TS (seq (iter xs (seq s2 t2)) u2))))))

;;Behavior of unroll-body with loops (2)
(assert
 (forall ((p PidClass)
          (c Config)
          (q PidClass)
          (x Var)
          (y Var)
          (s1 Stmt)
          (t1 Stmt)
          (u1 Stmt)
          (s2 Stmt)
          (t2 Stmt)
          (u2 Stmt))
         (! (let ((c2 (two-procs empty p (seq s1 skip) q (seq s2 skip))))
          (=> (and (is-proc c p (seq (unroll-body x (seq s1 t1)) u1))
                   (is-proc c q (seq (unroll-body y (seq s2 t2)) u2))
                   (=> (and (TC c2) (TS (seq s1 skip)) (TS (seq s2 skip))
                        (not (= p q)))
                       (Rewrite c2 empty)))
              (rewrite-2-rule c p (ite (= t1 (var x)) skip (seq (unroll-body x t1) u1))
                                q (ite (= t2 (var y)) skip (seq (unroll-body y t2) u2)))))
          :pattern
          ((TC c) 
           (TP p)
           (TP q)
           (TS (seq (unroll-body x (seq s1 t1)) u1))
           (TS (seq (unroll-body y (seq s2 t2)) u2))))))

;; Behavior of unroll-end with itself
(assert
 (forall ((p PidClass)
          (c Config)
          (q PidClass)
          (x Var)
          (y Var)
          (s1 Stmt)
          (t1 Stmt)
          (u1 Stmt)
          (s2 Stmt)
          (t2 Stmt)
          (u2 Stmt))
         (! (let ((c2 (two-procs empty p (seq s1 skip) q (seq s2 skip))))
          (=> (and (is-proc c p (seq (unroll-end x (seq s1 t1)) u1))
                   (is-proc c q (seq (unroll-end y (seq s2 t2)) u2))
                   (=> (and (TC c2) (TS (seq s1 skip)) (TS (seq s2 skip))
                        (not (= p q)))
                       (Rewrite c2 empty)))
              (rewrite-2-rule c p (ite (= t1 skip) skip (seq (unroll-end x t1) u1))
                                q (ite (= t2 skip) skip (seq (unroll-end y t2) u2)))))
          :pattern
          ((TC c) 
           (TP p)
           (TP q)
           (TS (seq (unroll-end x (seq s1 t1)) u1))
           (TS (seq (unroll-end y (seq s2 t2)) u2))))))

;; Behavior of unroll-end with unroll-body
(assert
 (forall ((p PidClass)
          (c Config)
          (q PidClass)
          (x Var)
          (y Var)
          (s1 Stmt)
          (t1 Stmt)
          (u1 Stmt)
          (s2 Stmt)
          (t2 Stmt)
          (u2 Stmt))
         (! (let ((c2 (two-procs empty p (seq s1 skip) q (seq s2 skip))))
          (=> (and (is-proc c p (seq (unroll-end x (seq s1 t1)) u1))
                   (is-proc c q (seq (unroll-body y (seq s2 t2)) u2))
                   (=> (and (TC c2) (TS (seq s1 skip)) (TS (seq s2 skip))
                        (not (= p q)))
                       (Rewrite c2 empty)))
              (rewrite-2-rule c p (ite (= t1 skip) skip (seq (unroll-end x t1) u1))
                                q (ite (= t2 (var y)) skip (seq (unroll-body y t2) u2)))))
          :pattern
          ((TC c) 
           (TP p)
           (TP q)
           (TS (seq (unroll-end x (seq s1 t1)) u1))
           (TS (seq (unroll-body y (seq s2 t2)) u2))))))



;; External choice
(assert
 (forall ((p PidClass)
          (p1 Stmt)
          (p2 Stmt)
          (p3 Stmt)
          (c Config))
         (!
          (let ((c1 (store c p (seq p1 p3)))
                (c2 (store c p (seq p2 p3))))
          (=> (is-proc c p (seq (offer p1 p2) p3))
              (and (Rewrite c c1)
                   (Rewrite c c2)
                   (TC c1)
                   (TC c2)
                   (TS (seq p1 p3)) (TS (seq p2 p3)))))
          :pattern
          ((TC c)
           (TP p)
           (TS (seq (offer p1 p2) p3))))))

;; Local Variables:
;; smtlib-include: ""
;; End:
