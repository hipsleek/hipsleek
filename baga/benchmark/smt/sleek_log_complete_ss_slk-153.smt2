(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node2 0)
(declare-fun val () (Field node2 Int))
(declare-fun left () (Field node2 node2))
(declare-fun right () (Field node2 node2))

(define-fun complete ((?in node2) (?n Int) (?nmin Int))
Space (tospace
(or
(or
(and 
(= ?in nil)
(= ?n 0)
(= ?nmin 0)

)(exists ((?flted_25_33 Int)(?flted_25_34 Int))(and 
(= (+ ?flted_25_34 1) ?n)
(= (+ ?flted_25_33 2) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref left ?l) (ref right ?r) ))
(complete ?l ?flted_25_34 ?nmin1)
(complete ?r ?flted_25_33 ?nmin2)
) )
)))(exists ((?flted_26_35 Int)(?flted_26_36 Int))(and 
(= (+ ?flted_26_36 1) ?n)
(= (+ ?flted_26_35 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref left ?l) (ref right ?r) ))
(complete ?l ?flted_26_36 ?nmin1)
(complete ?r ?flted_26_35 ?nmin2)
) )
)))))









































































































































































(declare-fun Anon13 () Int)
(declare-fun l13 () node2)
(declare-fun r13 () node2)
(declare-fun nmin () Int)
(declare-fun n () Int)
(declare-fun v20prm () node2)
(declare-fun v () node2)
(declare-fun tprm () node2)
(declare-fun t () node2)
(declare-fun nmin56 () Int)
(declare-fun flted29 () Int)
(declare-fun nmin58 () Int)
(declare-fun n20 () Int)
(declare-fun nmin59 () Int)
(declare-fun n21 () Int)
(declare-fun nmin57 () Int)
(declare-fun flted28 () Int)
(declare-fun nmin60 () Int)
(declare-fun n22 () Int)
(declare-fun nmin61 () Int)
(declare-fun n23 () Int)
(declare-fun v30prm () Int)
(declare-fun v28prm () Int)


(assert 
(and 
;lexvar(<= n21 nmin58)
(= (+ flted29 1) n)
(= (+ flted28 1) n)
(distinct tprm nil)
(= nmin n)
(= v20prm v)
(= tprm t)
(= n20 flted29)
(= nmin58 nmin56)
(<= 0 nmin56)
(<= nmin56 flted29)
(= n21 n20)
(= nmin59 nmin58)
(<= 0 nmin58)
(<= nmin58 n20)
(<= 0 nmin59)
(<= nmin59 n21)
(= n22 flted28)
(= nmin60 nmin57)
(<= 0 nmin57)
(<= nmin57 flted28)
(= v28prm nmin60)
(= n23 n22)
(= nmin61 nmin60)
(<= 0 nmin60)
(<= nmin60 n22)
(= v30prm n23)
(<= 0 nmin61)
(<= nmin61 n23)
(<= v30prm v28prm)
(tobool (ssep 
(pto tprm (sref (ref val Anon13) (ref left l13) (ref right r13) ))
(complete l13 n21 nmin59)
(complete r13 n23 nmin61)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)