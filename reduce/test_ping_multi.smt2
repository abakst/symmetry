;; Test?
(push)
(declare-const me Pid)
(declare-const ps PidSet)
(declare-const qs PidSet)
(declare-const q Pid)
(declare-const c Config)
(declare-fun ping (Pid) U)
(declare-fun pong (Pid) U)

(assert (forall ((s Subst) (p Pid))
                (= (apply-subst-u s (ping p))
                   (ping (select s p)))))

(assert (forall ((s Subst) (p Pid))
                (= (apply-subst-u s (pong p))
                   (pong (select s p)))))

(assert (forall ((p Pid) (q Pid))
                (=> (= (ping p) (ping q)) (= p q))))

(assert (forall ((p Pid) (q Pid))
                (=> (= (pong p) (pong q)) (= p q))))

(assert (forall ((p Pid) (q Pid))
                (not (= (ping p) (pong q)))))

(define-fun me_session () Stmt 
  (seq (foreach ps (seq (send (In ps) (ping me)) skip))
       (seq (foreach ps
               (bind q (seq (recv (pong q)) skip))) skip)))
                        
(define-fun p_session () Stmt
  (bind q (seq (recv (ping q)) (seq (send q (pong (In ps))) skip))))

(assert (not (= me q)))

(assert (= c (store (store empty (Sing me)  me_session)
                                 (Multi ps) p_session)))
;; Check validity...

(assert
 (TC c))
(assert
 (TS me_session))
(assert
 (TS p_session))
(assert
 (TP (Sing me)))
(assert
 (TP (Multi ps)))
(assert
 (TP (Multi qs)))
(assert
 (TP (Sing q)))
(assert
 (TV me))
(assert
 (TV (In ps)))
(assert
 (OKPidSet ps))
(assert
 (OKPidSet qs))

(assert
 (not (Rewrite c empty)))
(check-sat)
(pop)

;; Local Variables:
;; smtlib-include: "reduce.smt2"
;; End:
