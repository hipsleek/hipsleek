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










































































(declare-fun v9prm () node)
(declare-fun q3 () node)
(declare-fun flted3 () Int)
(declare-fun qs3 () Int)
(declare-fun ql3 () Int)
(declare-fun qmin3 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun res () node)
(declare-fun xs () Int)
(declare-fun xl () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= res v9prm)
(= v9prm q3)
(= (+ flted3 1) n)
(<= qmin3 qs3)
(<= ql3 xl)
(<= xs qmin3)
(= xprm x)
(distinct x nil)
(tobool (ssep 
(pto xprm (sref (ref val qmin3) (ref next q3) ))
(sll q3 flted3 qs3 ql3)
) )
)
)

(assert (not 
(exists ((flted4 Int)(sres3 Int)(lres3 Int))(and 
(<= lres3 xl)
(<= xs sres3)
(= (+ flted4 1) n)
(<= xs xl)
(<= 0 n)
(tobool  
(sll res flted4 sres3 lres3)
 )
))
))

(check-sat)