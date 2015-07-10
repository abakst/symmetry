(push)
(declare-const p1 Pid)
(declare-const p2 Pid)
(declare-const d Config)
(declare-const ps PidSet)
(declare-const m U)

(define-fun s1 () Stmt 
  (seq (foreach ps (seq (recv m) skip)) skip))

(define-fun s2 () Stmt
  (seq (send p1 m) skip))

(assert (= d (store (store empty (Sing  p1) s1)
                                 (Multi ps) s2)))

(assert (OKPidSet ps))
(assert (TV p1))
(assert (TV p2))

(assert (forall ((ps2 PidSet)) (= ps ps2)))

(assert (TC d))
(assert (TP (Sing p1)))
(assert (TP (Multi ps)))
(assert (TS s1))
(assert (TS s2))

(assert
 (not (Rewrite d empty)))

(check-sat)
(pop)
