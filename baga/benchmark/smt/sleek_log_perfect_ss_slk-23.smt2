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






























































(declare-fun Anon_342 () Int)
(declare-fun Anon1_343 () Int)
(declare-fun l_344 () node2)
(declare-fun r_345 () node2)
(declare-fun t () node2)
(declare-fun tprm () node2)
(declare-fun flted_340 () Int)
(declare-fun flted1_341 () Int)
(declare-fun n () Int)


(assert 
(exists ((flted Int)(flted1 Int)(Anon Int)(Anon1 Int)(l node2)(r node2))(and 
;lexvar(= tprm t)
(distinct tprm nil)
(= (+ flted 1) n)
(= (+ flted1 1) n)
(tobool (ssep 
(pto tprm (sref (ref val Anon) (ref flag Anon1) (ref left l) (ref right r) ))
(perfect l flted1)
(perfect r flted)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref val valprm) (ref flag flagprm) (ref left leftprm) (ref right rightprm) ))
 )
)
))

(check-sat)