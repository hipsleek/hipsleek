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










































































(declare-fun q4_886 () node)
(declare-fun x () node)
(declare-fun vprm () node)
(declare-fun v () node)
(declare-fun xprm () node)
(declare-fun sm () Int)
(declare-fun ql4_884 () Int)
(declare-fun lg () Int)
(declare-fun qmin4_885 () Int)
(declare-fun qs4_883 () Int)
(declare-fun flted5_882 () Int)
(declare-fun n () Int)


(assert 
(exists ((flted5 Int)(qs4 Int)(ql4 Int)(qmin4 Int)(q4 node))(and 
;lexvar(= xprm x)
(= vprm v)
(distinct xprm nil)
(<= sm qmin4)
(<= ql4 lg)
(<= qmin4 qs4)
(= (+ flted5 1) n)
(tobool (ssep 
(sll q4 flted5 qs4 ql4)
(pto xprm (sref (ref val qmin4) (ref next q4) ))
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