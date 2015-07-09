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

; Congruence
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


;; Triggers/Dummies
(declare-fun TC (Config) Bool)
(declare-fun TV (Pid) Bool)
(declare-fun TS (Stmt) Bool)
(declare-fun TP (PidClass) Bool)
(declare-fun OKSet(Set) Bool)
(declare-fun OKPidSet(PidSet) Bool)

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

(assert
 (forall ((p PidClass)
          (ps PidSet)
          (q Pid)
          (r Pid)
          (c Config)
          (s Stmt)
          (t Stmt))
         (! (=>
             (is-proc c p (seq (foreach ps (bind q s)) t))
             (rewrite-1-rule
              c
              p
              (seq (foreach ps (apply-subst (subst1 q r) s)) t)))
            :pattern
            ((OKPidSet ps) 
             (TC c) (TP p) (TV r) 
             (TS (seq (foreach ps (bind q s)) t))))))

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
              (not (= p1 p2))
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
          (m U)
          (c1 Config))
         (! (=>
             (and
              (not (= p1 p2))
              (= (size xs) (size ys))
              (is-proc c1 (Sing p1) (iter xs (seq (send p2 m) s1)))
              (is-proc c1 (Sing p2) (iter ys (seq (recv m) s2))))
             (rewrite-2-rule
              c1
              (Sing p1) (iter xs s1)
              (Sing p2) (iter ys s2)))
         :pattern 
         ((OKSet xs)
          (TC c1)
          (TS (iter xs (seq (send p2 m) s1)))
          (TS (iter ys (seq (recv m) s2)))
          (TP (Sing p1))
          (TP (Sing p2))))))


;; Parallel/Sequential
(assert
 (forall ((p1 Pid)
          (ps PidSet)
          (s1 Stmt)
          (s2 Stmt)
          (t Stmt)
          (m U)
          (c1 Config))
         (! (=>
             (and (is-proc c1 (Sing p1) 
                           (seq (foreach ps (seq (send (In ps) m) s1)) s2))
                  (is-proc c1 (Multi ps)
                           (seq (recv m) t)))
             (rewrite-2-rule
              c1
              (Sing p1) (seq (foreach ps s1) s2)
              (Multi ps) t))
         :pattern 
         ((OKPidSet ps)
          (TC c1)
          (TP (Sing p1))
          (TP (Multi ps))
          (TS (seq (foreach ps (seq (send (In ps) m) s1)) s2))
          (TS (seq (recv m) t))))))

;; Parallel/Sequential 2
(assert
 (forall ((p1 Pid)
          (ps PidSet)
          (s1 Stmt)
          (s2 Stmt)
          (t Stmt)
          (m U)
          (c1 Config))
         (! (=>
             (and (is-proc c1 
                           (Sing p1)  
                           (seq (foreach ps (seq (recv m) s1)) s2))
                  (is-proc c1 
                           (Multi ps) 
                           (seq (send p1 m) t)))
             (rewrite-2-rule c1 
                             (Sing p1) (seq (foreach ps s1) s2)
                             (Multi ps) t))
         :pattern 
         ((OKPidSet ps)
          (TC c1)
          (TP (Sing p1))
          (TP (Multi ps))
          (TS (seq (foreach ps (seq (recv m) s1)) s2))
          (TS (seq (send p1 m) t))))))

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
