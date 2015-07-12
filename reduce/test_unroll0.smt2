(push)
(declare-const p1 Pid)
(declare-const p2 Pid)
(declare-const x Var)
(declare-const xs Set)
(declare-const m U)

(define-fun sloop () Stmt
  (seq (var x) skip))

(define-fun s1 () Stmt
  (seq (unroll-body x sloop) skip))

(define-fun s2 () Stmt
  skip)

(define-fun c () Config
  (two-procs empty (Sing p1) s1 (Sing p2) s2))

(assert (TC c))
(assert (OKSet xs))
(assert (TS s1))
(assert (TS s2))
(assert (TP (Sing p1)))
(assert (TP (Sing p2)))

(assert (not (Rewrite c empty)))
(check-sat)
(pop)
