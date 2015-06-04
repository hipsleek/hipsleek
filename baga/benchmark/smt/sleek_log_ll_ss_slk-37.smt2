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
















































































































































































































































(declare-fun Anon5 () Int)
(declare-fun q5 () node)
(declare-fun Anon7 () Int)
(declare-fun v15prm () node)
(declare-fun q7 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun a () Int)
(declare-fun aprm () Int)
(declare-fun n () NUM)
(declare-fun flted11 () Int)
(declare-fun flted9 () Int)


(assert 
(and 
;lexvar(= v15prm q7)
(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(= aprm 1)
(= (+ flted9 1) n)
(= (+ flted11 1) flted9)
(tobool (ssep 
(pto xprm (sref (ref val Anon5) (ref next q5) ))
(pto q5 (sref (ref val Anon7) (ref next q7) ))
(ll q7 flted11)
) )
)
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val8prm) (ref next next8prm) ))
 )
)
))

(check-sat)