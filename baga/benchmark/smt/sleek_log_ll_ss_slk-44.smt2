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
















































































































































































































































(declare-fun Anon9 () Int)
(declare-fun q9 () node)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun v18_989 () Int)
(declare-fun aprm () Int)
(declare-fun flted13 () Int)
(declare-fun flted15_988 () Int)
(declare-fun n5 () Int)
(declare-fun x () node)
(declare-fun n () Int)


(assert 
(exists ((flted15 Int)(v18prm Int))(and 
;lexvar(= (+ flted13 1) n)
(distinct aprm 1)
(< 0 a)
(< a n)
(= aprm a)
(= xprm x)
(= (+ v18prm 1) aprm)
(= n5 flted13)
(<= 0 flted13)
(= (+ flted15 1) n5)
(<= 0 n5)
(tobool (ssep 
(pto xprm (sref (ref val Anon9) (ref next q9) ))
(ll q9 flted15)
) )
))
)

(assert (not 
(exists ((flted14 Int))(and 
(= (+ flted14 1) n)
(<= 0 n)
(tobool  
(ll x flted14)
 )
))
))

(check-sat)