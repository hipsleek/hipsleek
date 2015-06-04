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










































































(declare-fun q2_732 () node)
(declare-fun flted2_728 () Int)
(declare-fun n () Int)
(declare-fun qs2_729 () Int)
(declare-fun ql2_730 () Int)
(declare-fun xl () Int)
(declare-fun xs () Int)
(declare-fun qmin2_731 () Int)
(declare-fun xprm () node)
(declare-fun x () node)


(assert 
(exists ((flted2 Int)(qs2 Int)(ql2 Int)(qmin2 Int)(q2 node))(and 
;lexvar(= (+ flted2 1) n)
(<= qmin2 qs2)
(<= ql2 xl)
(<= xs qmin2)
(= xprm x)
(distinct x nil)
(tobool (ssep 
(sll q2 flted2 qs2 ql2)
(pto xprm (sref (ref val qmin2) (ref next q2) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val5prm) (ref next next5prm) ))
 )
)
))

(check-sat)