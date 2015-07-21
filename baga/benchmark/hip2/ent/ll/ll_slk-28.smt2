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


















































































































































































































(declare-fun Anon13 () Int)
(declare-fun Anon14_766 () Int)
(declare-fun q14_767 () node)
(declare-fun v20prm () node)
(declare-fun q13 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun n () Int)
(declare-fun flted22_765 () Int)
(declare-fun flted21 () Int)


(assert 
(exists ((flted22 Int)(Anon14 Int)(q14 node))(and 
;lexvar(= v20prm q13)
(= (+ flted21 1) n)
(= xprm x)
(< 1 n)
(= (+ flted22 1) flted21)
(tobool (ssep 
(pto xprm (sref (ref val Anon13) (ref next q13) ))
(pto v20prm (sref (ref val Anon14) (ref next q14) ))
(ll q14 flted22)
) )
))
)

(assert (not 
(and 
(tobool  
(pto v20prm (sref (ref val val13prm) (ref next next13prm) ))
 )
)
))

(check-sat)