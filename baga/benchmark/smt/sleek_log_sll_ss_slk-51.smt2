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

(define-fun sll ((?in node) (?n Int) (?sm NUM) (?lg Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)
(<= ?sm ?lg)

)(exists ((?flted_16_26 Int)(?qs_27 Int)(?ql_28 Int))(and 
(= (+ ?flted_16_26 1) ?n)
(<= ?qmin ?qs_27)
(<= ?ql_28 ?lg)
(<= ?sm ?qmin)
(tobool (ssep 
(pto ?in (sref (ref val ?qmin) (ref next ?q) ))
(sll ?q ?flted_16_26 ?qs_27 ?ql_28)
) )
)))))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_11_30 Int))(and 
(= (+ ?flted_11_30 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q ?flted_11_30)
) )
)))))










































































(declare-fun q6_1433 () node)
(declare-fun Anon () node)
(declare-fun v21prm () Int)
(declare-fun v () Int)
(declare-fun x () node)
(declare-fun vnprm () node)
(declare-fun vn () node)
(declare-fun xprm () node)
(declare-fun sm () Int)
(declare-fun ql6_1431 () Int)
(declare-fun lg () Int)
(declare-fun qmin6_1432 () Int)
(declare-fun qs6_1430 () Int)
(declare-fun flted10_1429 () Int)
(declare-fun n () Int)


(assert 
(exists ((flted10 Int)(qs6 Int)(ql6 Int)(qmin6 Int)(q6 node))(and 
;lexvar(= v21prm v)
(= xprm x)
(= vnprm vn)
(distinct xprm nil)
(<= sm qmin6)
(<= ql6 lg)
(<= qmin6 qs6)
(= (+ flted10 1) n)
(tobool (ssep 
(sll q6 flted10 qs6 ql6)
(pto xprm (sref (ref val qmin6) (ref next q6) ))
(pto vn (sref (ref val v) (ref next Anon) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val11prm) (ref next next11prm) ))
 )
)
))

(check-sat)