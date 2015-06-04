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










































































(declare-fun q5 () node)
(declare-fun v18prm () node)
(declare-fun x () node)
(declare-fun xprm () node)
(declare-fun ql5 () Int)
(declare-fun qs5 () Int)
(declare-fun flted6 () Int)
(declare-fun vprm () Int)
(declare-fun qmin5 () Int)
(declare-fun res () node)
(declare-fun v () Int)
(declare-fun sm () Int)
(declare-fun lg () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= res v18prm)
(= xprm x)
(= vprm v)
(distinct xprm nil)
(<= sm qmin5)
(<= ql5 lg)
(<= qmin5 qs5)
(= (+ flted6 1) n)
(<= vprm qmin5)
(tobool (ssep 
(sll q5 flted6 qs5 ql5)
(pto xprm (sref (ref val qmin5) (ref next q5) ))
(pto v18prm (sref (ref val vprm) (ref next xprm) ))
) )
)
)

(assert (not 
(exists ((flted8 Int)(mi1 Int)(ma1 Int))(and 
;eqmax;eqmin(= flted8 (+ 1 n))
(<= sm lg)
(<= 0 n)
(tobool  
(sll res flted8 mi1 ma1)
 )
))
))

(check-sat)