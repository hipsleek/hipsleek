(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node2 0)
(declare-fun val () (Field node2 Int))
(declare-fun flag () (Field node2 Int))
(declare-fun left () (Field node2 node2))
(declare-fun right () (Field node2 node2))

(define-fun perfect ((?in node2) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_28_29 Int)(?flted_28_30 Int))(and 
(= (+ ?flted_28_30 1) ?n)
(= (+ ?flted_28_29 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref flag ?Anon_15) (ref left ?l) (ref right ?r) ))
(perfect ?l ?flted_28_30)
(perfect ?r ?flted_28_29)
) )
)))))






























































(declare-fun Anon6 () Int)
(declare-fun l3 () node2)
(declare-fun r3 () node2)
(declare-fun n5 () Int)
(declare-fun aprm () node2)
(declare-fun a () node2)
(declare-fun tprm () node2)
(declare-fun flted6 () Int)
(declare-fun Anon7 () Int)
(declare-fun flted7 () Int)
(declare-fun n6 () Int)
(declare-fun res () node2)
(declare-fun v33prm () node2)
(declare-fun t () node2)
(declare-fun n () Int)


(assert 
(and 
;lexvar(<= 0 n5)
(<= 0 flted6)
(= n5 flted6)
(= tprm t)
(= aprm a)
(distinct tprm nil)
(= (+ flted7 1) n)
(= (+ flted6 1) n)
(distinct Anon7 0)
(= n6 flted7)
(<= 0 flted7)
(<= 0 n6)
(= res v33prm)
(tobool (ssep 
(pto tprm (sref (ref val Anon6) (ref flag Anon7) (ref left l3) (ref right r3) ))
(perfect l3 n5)
(perfect r3 n6)
) )
)
)

(assert (not 
(exists ((n7 Int))(and 
(= n7 n)
(<= 0 n)
(tobool  
(perfect t n7)
 )
))
))

(check-sat)