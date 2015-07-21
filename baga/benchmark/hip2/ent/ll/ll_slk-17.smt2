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


















































































































































































































(declare-fun Anon4_460 () Int)
(declare-fun q4_461 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun a () Int)
(declare-fun aprm () Int)
(declare-fun flted8_459 () Int)
(declare-fun n () NUM)


(assert 
(exists ((flted8 Int)(Anon4 Int)(q4 node))(and 
;lexvar(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(= aprm 1)
(= (+ flted8 1) n)
(tobool (ssep 
(pto xprm (sref (ref val Anon4) (ref next q4) ))
(ll q4 flted8)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val6prm) (ref next next6prm) ))
 )
)
))

(check-sat)