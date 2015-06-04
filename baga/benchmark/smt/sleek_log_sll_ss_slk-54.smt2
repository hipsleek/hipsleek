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










































































(declare-fun q7 () node)
(declare-fun Anon () node)
(declare-fun x () node)
(declare-fun vnprm () node)
(declare-fun vn () node)
(declare-fun xprm () node)
(declare-fun sm () Int)
(declare-fun ql7 () Int)
(declare-fun lg () Int)
(declare-fun qs7 () Int)
(declare-fun flted11 () Int)
(declare-fun n () Int)
(declare-fun v () Int)
(declare-fun qmin7 () Int)


(assert 
(and 
;lexvar(= xprm x)
(= vnprm vn)
(distinct xprm nil)
(<= sm qmin7)
(<= ql7 lg)
(<= qmin7 qs7)
(= (+ flted11 1) n)
(<= v qmin7)
(tobool (ssep 
(sll q7 flted11 qs7 ql7)
(pto xprm (sref (ref val qmin7) (ref next q7) ))
(pto vn (sref (ref val v) (ref next Anon) ))
) )
)
)

(assert (not 
(and 
(tobool  
(pto vnprm (sref (ref val val12prm) (ref next next12prm) ))
 )
)
))

(check-sat)