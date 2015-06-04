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
















































































































































































































































(declare-fun Anon13 () Int)
(declare-fun q13 () node)
(declare-fun Anon15 () Int)
(declare-fun v21prm () node)
(declare-fun q15 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun flted23 () Int)
(declare-fun flted21 () Int)
(declare-fun res () node)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= res v21prm)
(= v21prm q15)
(= (+ flted21 1) n)
(= xprm x)
(< 1 n)
(= (+ flted23 1) flted21)
(tobool (ssep 
(pto xprm (sref (ref val Anon13) (ref next q13) ))
(pto q13 (sref (ref val Anon15) (ref next q15) ))
(ll q15 flted23)
) )
)
)

(assert (not 
(exists ((flted24 Int))(and 
(= (+ flted24 2) n)
(<= 0 n)
(tobool  
(ll res flted24)
 )
))
))

(check-sat)