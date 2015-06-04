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
















































































































































































































































(declare-fun Anon3 () Int)
(declare-fun n2 () Int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun flted5 () Int)
(declare-fun n1 () Int)
(declare-fun q3 () node)
(declare-fun v3prm () node)


(assert 
(and 
;lexvar(< 0 n1)
(= yprm y)
(= xprm x)
(= (+ flted5 1) n1)
(= v3prm q3)
(= v3prm nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon3) (ref next q3) ))
(ll q3 flted5)
(ll y n2)
) )
)
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)