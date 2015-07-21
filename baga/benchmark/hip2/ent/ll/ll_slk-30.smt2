(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/hip/
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

)(exists ((?flted_14_24 Int))(and 
(= (+ ?flted_14_24 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref next ?q) ))
(ll ?q ?flted_14_24)
) )
)))))


















































































































































































































(declare-fun Anon16_819 () Int)
(declare-fun q16_820 () node)
(declare-fun flted25_818 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun n () Int)
(declare-fun tmpprm () node)


(assert 
(exists ((flted25 Int)(Anon16 Int)(q16 node))(and 
;lexvar(= (+ flted25 1) n)
(= xprm x)
(= aprm a)
(< 0 n)
(= tmpprm nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon16) (ref next q16) ))
(ll q16 flted25)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val14prm) (ref next next14prm) ))
 )
)
))

(check-sat)