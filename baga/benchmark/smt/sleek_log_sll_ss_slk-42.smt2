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










































































(declare-fun v16prm () node)
(declare-fun v17_1087 () node)
(declare-fun x () node)
(declare-fun vprm () Int)
(declare-fun xprm () node)
(declare-fun res () node)
(declare-fun v () Int)
(declare-fun sm () Int)
(declare-fun lg () Int)
(declare-fun n () Int)


(assert 
(exists ((v17prm node))(and 
;lexvar(= res v16prm)
(= v17prm nil)
(= xprm x)
(= vprm v)
(= xprm nil)
(tobool (ssep 
(sll x n sm lg)
(pto v16prm (sref (ref val vprm) (ref next v17prm) ))
) )
))
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