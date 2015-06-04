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
















































































































































































































































(declare-fun Anon8_834 () Int)
(declare-fun q8_835 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun a () Int)
(declare-fun aprm () Int)
(declare-fun flted12_833 () Int)
(declare-fun n () NUM)


(assert 
(exists ((flted12 Int)(Anon8 Int)(q8 node))(and 
;lexvar(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(distinct aprm 1)
(= (+ flted12 1) n)
(tobool (ssep 
(pto xprm (sref (ref val Anon8) (ref next q8) ))
(ll q8 flted12)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val9prm) (ref next next9prm) ))
 )
)
))

(check-sat)