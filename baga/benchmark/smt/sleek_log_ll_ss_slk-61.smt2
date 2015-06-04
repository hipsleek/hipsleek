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
















































































































































































































































(declare-fun Anon17 () Int)
(declare-fun q17 () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun xprm () node)
(declare-fun flted26 () Int)
(declare-fun flted28_1426 () Int)
(declare-fun n6 () Int)
(declare-fun x () node)
(declare-fun n () Int)


(assert 
(exists ((flted28 Int))(and 
;lexvar(distinct q17 nil)
(< 0 n)
(= aprm a)
(= xprm x)
(= (+ flted26 1) n)
(= n6 flted26)
(<= 0 flted26)
(= flted28 (+ 1 n6))
(<= 0 n6)
(tobool (ssep 
(pto xprm (sref (ref val Anon17) (ref next q17) ))
(ll q17 flted28)
) )
))
)

(assert (not 
(exists ((flted27 Int))(and 
(= flted27 (+ 1 n))
(<= 0 n)
(tobool  
(ll x flted27)
 )
))
))

(check-sat)