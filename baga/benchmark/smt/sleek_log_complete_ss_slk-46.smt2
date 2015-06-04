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









































































































































































(declare-fun Anon7 () Int)
(declare-fun r7 () node2)
(declare-fun v12prm () node2)
(declare-fun l7 () node2)
(declare-fun t () node2)
(declare-fun tprm () node2)
(declare-fun nmin () Int)
(declare-fun nmin19 () Int)
(declare-fun nmin20 () Int)
(declare-fun flted14 () Int)
(declare-fun flted15 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= v12prm l7)
(= tprm t)
(distinct tprm nil)
(= (+ flted14 1) n)
(= (+ flted15 1) n)
(tobool (ssep 
(pto tprm (sref (ref val Anon7) (ref left l7) (ref right r7) ))
(complete l7 flted15 nmin19)
(complete r7 flted14 nmin20)
) )
)
)

(assert (not 
(and 
(tobool  
(complete v12prm n4 nmin18)
 )
)
))

(check-sat)