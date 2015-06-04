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










































































(declare-fun tmpprm () node)
(declare-fun q5 () node)
(declare-fun x () node)
(declare-fun v () Int)
(declare-fun xprm () node)
(declare-fun sm () Int)
(declare-fun ql5 () Int)
(declare-fun lg () Int)
(declare-fun qs5 () Int)
(declare-fun flted6 () Int)
(declare-fun n () Int)
(declare-fun qmin5 () Int)
(declare-fun vprm () Int)


(assert 
(and 
;lexvar(= tmpprm q5)
(= xprm x)
(= vprm v)
(distinct xprm nil)
(<= sm qmin5)
(<= ql5 lg)
(<= qmin5 qs5)
(= (+ flted6 1) n)
(< qmin5 vprm)
(tobool (ssep 
(pto xprm (sref (ref val qmin5) (ref next q5) ))
(sll q5 flted6 qs5 ql5)
) )
)
)

(assert (not 
(and 
(tobool  
(sll tmpprm n3 sm1 lg1)
 )
)
))

(check-sat)