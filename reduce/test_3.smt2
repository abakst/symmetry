(push)
(declare-const p1 Pid)
(declare-const p2 Pid)
(declare-const d Config)
(declare-const xs Set)
(declare-const ys Set)
(declare-const m U)

(define-fun s3 () Stmt 
  (iter xs
        (seq (send p2 m) 
             (seq (recv m) 
                  skip))))
  
(define-fun s4 () Stmt
  (iter ys
   (seq (recv m) 
        (seq (send p1 m) 
             skip))))

(assert (not (= p1 p2)))
(assert (= d (store (store empty (Sing p1) s3)
                                 (Sing p2) s4)))
(assert (= (size xs) (size ys)))
(assert (OKSet xs))
(assert (OKSet ys))
(assert
 (TC d))
(assert
 (TS s3))
(assert
 (TS s4))
(assert
 (TP (Sing p1)))
(assert
 (TP (Sing p2)))
(assert
 (not (Rewrite d empty)))
(check-sat)
(pop)
