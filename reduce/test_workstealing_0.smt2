(push)
(declare-const p1 Pid)
(declare-const p2 Pid)
(declare-const p3 Pid)
(declare-const m1 U)
(declare-const m2 U)
(declare-const m3 U)
(assert (not (= p1 p2)))
(assert (not (= p1 p3)))
(assert (not (= p2 p3)))

(define-const p1_proc Stmt
  (seq (recv m1)
  (seq (send p2 m2)
  (seq (send p2 m3) skip))))

(define-const p2_proc Stmt
  (seq (send p1 m1)
  (seq (offer (seq (recv m2) (send p3 m2))
              (recv m3))
  (seq (offer (seq (recv m2) (send p3 m2))
              (recv m3))
       skip))))

(define-const p3_proc Stmt
  (seq (recv m2) skip))

(define-const c Config
  (store (store (store empty (Sing p1) p1_proc)
                (Sing p2) p2_proc)
         (Sing p3) p3_proc))
(assert (and (TC c)
             (TP (Sing p1))
             (TP (Sing p2))
             (TP (Sing p3))
             (TS p1_proc)
             (TS p2_proc)
             (TS p3_proc)))
(assert (not (Rewrite c empty)))
(check-sat)
(pop)
