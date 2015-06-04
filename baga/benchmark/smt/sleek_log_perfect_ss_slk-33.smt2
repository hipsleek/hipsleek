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






























































(declare-fun Anon2 () Int)
(declare-fun Anon3 () Int)
(declare-fun l1 () node2)
(declare-fun r1 () node2)
(declare-fun tprm () node2)
(declare-fun flted3 () Int)
(declare-fun flted2 () Int)
(declare-fun n2 () Int)
(declare-fun n3 () Int)
(declare-fun v19_642 () Int)
(declare-fun v20prm () Int)
(declare-fun t () node2)
(declare-fun res () Int)
(declare-fun n () Int)


(assert 
(exists ((v19prm Int))(and 
;lexvar(= (+ flted3 1) n)
(= (+ flted2 1) n)
(distinct tprm nil)
(= tprm t)
(= n2 flted3)
(<= 0 flted3)
(<= 0 n2)
(= n3 flted2)
(<= 0 flted2)
(<= 0 n3)
(= v20prm (+ 1 v19prm))
(= res v20prm)
(tobool (ssep 
(pto tprm (sref (ref val Anon2) (ref flag Anon3) (ref left l1) (ref right r1) ))
(perfect l1 n2)
(perfect r1 n3)
) )
))
)

(assert (not 
(exists ((n4 Int))(and 
(= n4 n)
(= res n)
(<= 0 n)
(tobool  
(perfect t n4)
 )
))
))

(check-sat)