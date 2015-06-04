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









































































































































































(declare-fun Anon3 () Int)
(declare-fun l3 () node2)
(declare-fun r3 () node2)
(declare-fun v6prm () Int)
(declare-fun v7prm () Int)
(declare-fun nmin10 () Int)
(declare-fun n2 () Int)
(declare-fun nmin7 () Int)
(declare-fun n1 () Int)
(declare-fun t () node2)
(declare-fun tprm () node2)
(declare-fun nmin () Int)
(declare-fun nmin8 () Int)
(declare-fun nmin9 () Int)
(declare-fun flted6 () NUM)
(declare-fun flted7 () NUM)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= v6prm 1)
(<= nmin10 n2)
(<= 0 nmin10)
(<= nmin9 flted6)
(<= 0 nmin9)
(= nmin10 nmin9)
(= n2 flted6)
(<= nmin7 n1)
(<= 0 nmin7)
(<= nmin8 flted7)
(<= 0 nmin8)
(= nmin7 nmin8)
(= n1 flted7)
(= tprm t)
(distinct tprm nil)
(= (+ flted6 1) n)
(= (+ flted7 1) n)
(tobool (ssep 
(pto tprm (sref (ref val Anon3) (ref left l3) (ref right r3) ))
(complete l3 n1 nmin7)
(complete r3 n2 nmin10)
) )
)
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)