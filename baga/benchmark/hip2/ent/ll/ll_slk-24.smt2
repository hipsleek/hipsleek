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


















































































































































































































(declare-fun Anon10_673 () Int)
(declare-fun q10_674 () node)
(declare-fun flted16_672 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun n () Int)


(assert 
(exists ((flted16 Int)(Anon10 Int)(q10 node))(and 
;lexvar(= (+ flted16 1) n)
(= xprm x)
(< 0 n)
(tobool (ssep 
(pto xprm (sref (ref val Anon10) (ref next q10) ))
(ll q10 flted16)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val10prm) (ref next next10prm) ))
 )
)
))

(check-sat)