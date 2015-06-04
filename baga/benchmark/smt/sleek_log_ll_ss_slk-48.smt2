(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_14_23 Int))(and 
(= (+ ?flted_14_23 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q ?flted_14_23)
) )
)))))
















































































































































































































































(declare-fun Anon12_1108 () Int)
(declare-fun q12_1109 () node)
(declare-fun flted20_1107 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun n () Int)


(assert 
(exists ((flted20 Int)(Anon12 Int)(q12 node))(and 
;lexvar(= (+ flted20 1) n)
(= xprm x)
(< 1 n)
(tobool (ssep 
(pto xprm (sref (ref val Anon12) (ref next q12) ))
(ll q12 flted20)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val12prm) (ref next next12prm) ))
 )
)
))

(check-sat)