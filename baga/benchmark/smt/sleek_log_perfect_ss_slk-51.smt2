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






























































(declare-fun l3 () node2)
(declare-fun r3 () node2)
(declare-fun flag () Int)
(declare-fun v26_1124 () Int)
(declare-fun val () node2)
(declare-fun Anon6 () node2)
(declare-fun Anon7 () Int)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun tprm () node2)
(declare-fun flted7 () Int)
(declare-fun flted6 () Int)
(declare-fun t () node2)
(declare-fun n () Int)


(assert 
(exists ((v26prm Int))(and 
;lexvar(= res v31prm)
(= flag Anon7)
(= v26prm 1)
(= val Anon6)
(= Anon7 0)
(= tprm t)
(= aprm a)
(distinct tprm nil)
(= (+ flted7 1) n)
(= (+ flted6 1) n)
(tobool (ssep 
(perfect l3 flted6)
(perfect r3 flted7)
(pto tprm (sref (ref val aprm) (ref flag v26prm) (ref left l3) (ref right r3) ))
) )
))
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