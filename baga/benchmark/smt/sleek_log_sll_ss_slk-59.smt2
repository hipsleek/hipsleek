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










































































(declare-fun next2 () node)
(declare-fun Anon () node)
(declare-fun v19_1694 () node)
(declare-fun x () node)
(declare-fun vnprm () node)
(declare-fun vn () node)
(declare-fun xprm () node)
(declare-fun res () node)
(declare-fun v () Int)
(declare-fun sm () Int)
(declare-fun lg () Int)
(declare-fun n () Int)


(assert 
(exists ((v19prm node))(and 
;lexvar(= res vnprm)
(= next2 Anon)
(= v19prm nil)
(= xprm x)
(= vnprm vn)
(= xprm nil)
(tobool (ssep 
(sll x n sm lg)
(pto vnprm (sref (ref val v) (ref next v19prm) ))
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