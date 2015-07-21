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


















































































































































































































(declare-fun Anon2_230 () Int)
(declare-fun q2_231 () node)
(declare-fun n2 () Int)
(declare-fun flted4_229 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun n1 () Int)


(assert 
(exists ((flted4 Int)(Anon2 Int)(q2 node))(and 
;lexvar(= (+ flted4 1) n1)
(= xprm x)
(= yprm y)
(< 0 n1)
(tobool (ssep 
(pto xprm (sref (ref val Anon2) (ref next q2) ))
(ll q2 flted4)
(ll y n2)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val3prm) (ref next next3prm) ))
 )
)
))

(check-sat)