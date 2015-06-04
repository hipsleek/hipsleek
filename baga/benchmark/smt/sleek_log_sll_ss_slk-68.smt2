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










































































(declare-fun q9 () node)
(declare-fun lg () node)
(declare-fun yl1 () node)
(declare-fun sm () node)
(declare-fun ys1 () node)
(declare-fun n5 () node)
(declare-fun m1 () node)
(declare-fun v27prm () Int)
(declare-fun Anon3 () Int)
(declare-fun x () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun flted16 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= lg yl1)
(= sm ys1)
(= n5 m1)
(= v27prm Anon3)
(= xprm x)
(= yprm y)
(distinct xprm nil)
(= (+ flted16 1) n)
(tobool (ssep 
(ll q9 flted16)
(pto xprm (sref (ref val Anon3) (ref next q9) ))
) )
)
)

(assert (not 
;lexvar
))

(check-sat)