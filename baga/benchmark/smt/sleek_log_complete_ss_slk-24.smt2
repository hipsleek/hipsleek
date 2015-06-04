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









































































































































































(declare-fun Anon2 () Int)
(declare-fun l2 () node2)
(declare-fun r2 () node2)
(declare-fun v5prm () Int)
(declare-fun nmin10 () Int)
(declare-fun n2 () Int)
(declare-fun v3prm () Int)
(declare-fun nmin7 () Int)
(declare-fun n1 () Int)
(declare-fun t () node2)
(declare-fun tprm () node2)
(declare-fun nmin () Int)
(declare-fun nmin5 () Int)
(declare-fun nmin6 () Int)
(declare-fun flted4 () NUM)
(declare-fun flted5 () NUM)
(declare-fun n () Int)


(assert 
(and 
;lexvar(<= nmin10 n2)
(<= 0 nmin10)
(= v5prm n2)
(<= nmin6 flted4)
(<= 0 nmin6)
(= nmin10 nmin6)
(= n2 flted4)
(<= nmin7 n1)
(<= 0 nmin7)
(= v3prm n1)
(<= nmin5 flted5)
(<= 0 nmin5)
(= nmin7 nmin5)
(= n1 flted5)
(= tprm t)
(distinct tprm nil)
(= (+ flted4 2) n)
(= (+ flted5 1) n)
(tobool (ssep 
(pto tprm (sref (ref val Anon2) (ref left l2) (ref right r2) ))
(complete l2 n1 nmin7)
(complete r2 n2 nmin10)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)