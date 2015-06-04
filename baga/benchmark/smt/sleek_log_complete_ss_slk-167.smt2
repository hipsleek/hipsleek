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









































































































































































(declare-fun tprm () node2)
(declare-fun v38_8694 () node2)
(declare-fun v37_8693 () node2)
(declare-fun t () node2)
(declare-fun v20prm () Int)
(declare-fun v () Int)
(declare-fun t1 () node2)
(declare-fun n () Int)
(declare-fun nmin () Int)


(assert 
(exists ((v37prm node2)(v38prm node2))(and 
;lexvar(= v38prm nil)
(= v37prm nil)
(= t1 t)
(= v20prm v)
(= nmin n)
(= t1 nil)
(tobool (ssep 
(pto tprm (sref (ref val v20prm) (ref left v37prm) (ref right v38prm) ))
(complete t n nmin)
) )
))
)

(assert (not 
(exists ((flted31 Int)(nmin67 Int))(and 
(= flted31 (+ 1 n))
(<= nmin n)
(<= 0 nmin)
(tobool  
(complete tprm flted31 nmin67)
 )
))
))

(check-sat)