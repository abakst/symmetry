(push)
(declare-const p1 Pid)
(declare-const p2 Pid)
(declare-const p3 Pid)
(assert (and (not (= p1 p2))
             (not (= p1 p3))
             (not (= p2 p3))))

(declare-const m U)
(define-const s1 Stmt
  (seq (send p2 m) 
  (seq (recv m) skip)))
(define-const s2 Stmt
  (seq (recv m) 
  (seq (send p3 m) skip)))
(define-const s3 Stmt
  (seq (recv m) 
  (seq (send p1 m) skip)))
(define-const c Config
  (store (store (store empty (Sing p1) s1)
                (Sing p2) s2)
         (Sing p3) s3))

(assert (and (TC c)
             (TP (Sing p1))
             (TP (Sing p2))
             (TP (Sing p3))
             (TS s1)
             (TS s2)
             (TS s3)))

(assert (not (Rewrite c empty)))
(check-sat)
(pop)
