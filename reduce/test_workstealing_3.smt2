(push)
(declare-const p1 Pid)
(declare-const p2 Pid)
(declare-const q Pid)
(declare-const xs Set)
(declare-const x Var)
(declare-fun pid (Pid) U)
(declare-const m2 U)
(declare-const m3 U)

(assert (forall ((p Pid))
                (and (not (= (pid p) m2))
                     (not (= m2 m3))
                     (not (= (pid p) m3)))))

(assert (forall ((p Pid))
                (or (= p p1)
                    (= p p2)
                    (= p q))))

(assert (not (= p1 p2)))
(assert (not (= p1 q)))
(assert (not (= p2 q)))

(assert (forall ((p Pid) (q Pid))
                (=> (= (pid p) (pid q)) (= p q))))

(assert (forall ((s Subst) (p Pid))
                (= (apply-subst-u s (pid p))
                   (pid (select s p)))))

(assert (forall ((s Subst))
                (= (apply-subst-u s m2) m2)))

(assert (forall ((s Subst))
                (= (apply-subst-u s m3) m3)))

(define-const p1_proc Stmt
  (bind q (seq (recv (pid q)) (seq (send q m3) skip))))

(define-const p2_proc Stmt
  (seq (send p1 (pid p2)) (seq (recv m3) skip)))

(define-const c Config
  (store (store empty (Sing p1) p1_proc)
                      (Sing p2) p2_proc))

(assert (and (TC c)
             (TP (Sing p1))
             (TP (Sing p2))
             (TV p2)
             (TV p1)
             (TS p1_proc)
             (TS p2_proc)))
(assert (not (Rewrite c empty)))
(check-sat)
(pop)
