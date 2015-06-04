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









































































































































































(declare-fun Anon10 () Int)
(declare-fun r10 () node2)
(declare-fun l10 () node2)
(declare-fun v23prm () Int)
(declare-fun nmin29 () Int)
(declare-fun n7 () Int)
(declare-fun t () node2)
(declare-fun v20prm () node2)
(declare-fun v () node2)
(declare-fun tprm () node2)
(declare-fun nmin () NUM)
(declare-fun nmin27 () Int)
(declare-fun nmin28 () Int)
(declare-fun flted20 () Int)
(declare-fun flted21 () NUM)
(declare-fun n () NUM)


(assert 
(and 
;lexvar(<= nmin29 n7)
(<= 0 nmin29)
(= v23prm nmin29)
(<= nmin27 flted21)
(<= 0 nmin27)
(= nmin29 nmin27)
(= n7 flted21)
(= tprm t)
(= v20prm v)
(< nmin n)
(distinct tprm nil)
(= (+ flted20 2) n)
(= (+ flted21 1) n)
(tobool (ssep 
(pto tprm (sref (ref val Anon10) (ref left l10) (ref right r10) ))
(complete r10 flted20 nmin28)
(complete l10 n7 nmin29)
) )
)
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref val val5prm) (ref left left5prm) (ref right right5prm) ))
 )
)
))

(check-sat)