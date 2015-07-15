(push)
(declare-const p1 Pid)
(declare-const p2 Pid)
(declare-const xs Set)
(declare-const x Var)
(declare-const m1 U)
(declare-const m2 U)
(declare-const m3 U)
(assert (not (= p1 p2)))

(define-const p1_loop Stmt
  (seq (recv m1) (seq (send p2 m3) (seq (var x) skip))))

(define-const p2_loop Stmt
  (seq (send p1 m1)
  (seq (offer (seq (recv m2) (var x)) (recv m3)) skip)))

(define-const p1_proc Stmt
  (seq (mu x p1_loop) skip))

(assert (= (unroll-body x p1_loop) p1_loop))
(assert (= (unroll-end x p1_loop) skip))
(assert (= (unroll-body x p2_loop) (seq (send p1 m1) (seq (recv m2) (seq (var x) skip)))))
(assert (= (unroll-end x p2_loop) (seq (send p1 m1) (seq (recv m3) skip))))

(define-const p2_proc Stmt
  (seq (mu x p2_loop) skip))

(define-const c Config
  (store (store empty (Sing p1) p1_proc)
         (Sing p2) p2_proc))

(assert (and (TC c)
             (TP (Sing p1))
             (TP (Sing p2))
             (TS p1_proc)
             (TS p2_proc)))
(assert (not (Rewrite c empty)))
(check-sat)
(pop)
