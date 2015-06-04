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
















































































































































































































































(declare-fun Anon_54 () Int)
(declare-fun q_55 () node)
(declare-fun n2 () Int)
(declare-fun flted_53 () Int)
(declare-fun n1 () Int)
(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)


(assert 
(exists ((flted Int)(Anon Int)(q node))(and 
;lexvar(= (+ flted 1) n1)
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon) (ref next q) ))
(ll q flted)
(ll y n2)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val valprm) (ref next nextprm) ))
 )
)
))

(check-sat)