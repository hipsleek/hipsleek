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










































































(declare-fun v25_1856 () node)
(declare-fun next4 () node)
(declare-fun q7 () node)
(declare-fun ma5 () Int)
(declare-fun mi5 () Int)
(declare-fun flted14 () Int)
(declare-fun Anon1 () node)
(declare-fun Anon () node)
(declare-fun v1 () Int)
(declare-fun lg2 () Int)
(declare-fun sm2 () Int)
(declare-fun n4 () Int)
(declare-fun x () node)
(declare-fun vnprm () node)
(declare-fun vn () node)
(declare-fun xprm () node)
(declare-fun ql7 () NUM)
(declare-fun qs7 () Int)
(declare-fun flted11 () Int)
(declare-fun qmin7 () Int)
(declare-fun res () node)
(declare-fun v () Int)
(declare-fun sm () Int)
(declare-fun lg () Int)
(declare-fun n () Int)


(assert 
(exists ((v25prm node))(and 
;lexvar(= res xprm)
(= next4 q7)
(<= sm2 lg2)
(<= 0 n4)
;eqmax;eqmin(= flted14 (+ 1 n4))
(<= qs7 ql7)
(<= 0 flted11)
(distinct vn nil)
(= Anon1 Anon)
(= v1 v)
(= lg2 ql7)
(= sm2 qs7)
(= n4 flted11)
(= xprm x)
(= vnprm vn)
(distinct xprm nil)
(<= sm qmin7)
(<= ql7 lg)
(<= qmin7 qs7)
(= (+ flted11 1) n)
(< qmin7 v)
(tobool (ssep 
(sll v25prm flted14 mi5 ma5)
(pto xprm (sref (ref val qmin7) (ref next v25prm) ))
) )
))
)

(assert (not 
(exists ((flted13 Int)(mi4 Int)(ma4 Int))(and 
;eqmax;eqmin(= flted13 (+ 1 n))
(<= sm lg)
(<= 0 n)
(tobool  
(sll res flted13 mi4 ma4)
 )
))
))

(check-sat)