(push)
(declare-const p1 Pid)
(declare-const p2 Pid)
(declare-const m1 U)
(declare-const m2 U)
(declare-const m3 U)
(assert (not (= p1 p2)))

(define-const s1 Stmt
  (seq (offer (seq (recv m1) (send p2 m3)) 
              (seq (recv m2) (send p2 m3))) skip))
(define-const s2 Stmt
  (seq (send p1 m2) (seq (recv m3) skip)))

(define-const c Config
  (two-procs empty (Sing p1) s1 (Sing p2) s2)) 
 
(assert (and (TC c)
             (TS s1)
             (TS s2)
             (TP (Sing p1))
             (TP (Sing p2))))

(assert (not (Rewrite c empty)))
(check-sat)
(pop)
