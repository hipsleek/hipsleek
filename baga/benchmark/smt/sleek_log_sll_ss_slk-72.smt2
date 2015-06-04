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










































































(declare-fun yprm () node)
(declare-fun Anon4_2201 () Int)
(declare-fun Anon5_2202 () Int)
(declare-fun q9 () node)
(declare-fun y1 () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun Anon3 () Int)
(declare-fun n5 () Int)
(declare-fun sm () Int)
(declare-fun lg () Int)
(declare-fun flted18 () Int)
(declare-fun mi7 () Int)
(declare-fun ma7 () Int)
(declare-fun flted16 () Int)
(declare-fun flted19_2200 () Int)
(declare-fun n6 () Int)
(declare-fun m () Int)
(declare-fun ys () Int)
(declare-fun yl () Int)
(declare-fun x () node)
(declare-fun ys1 () NUM)
(declare-fun yl1 () NUM)
(declare-fun m1 () Int)
(declare-fun n () Int)


(assert 
(exists ((flted19 Int)(Anon4 Int)(Anon5 Int))(and 
;lexvar(= (+ flted16 1) n)
(distinct xprm nil)
(= y1 y)
(= xprm x)
(= n5 m1)
(= sm ys1)
(= lg yl1)
(<= 0 m1)
(<= ys1 yl1)
(= flted18 (+ 1 n5))
;eqmin;eqmax(<= 0 n5)
(<= sm lg)
(= n6 flted16)
(= m flted18)
(= ys mi7)
(= yl ma7)
(<= 0 flted18)
(<= mi7 ma7)
(<= 0 flted16)
(= flted19 (+ m n6))
(<= 0 n6)
(<= 0 m)
(<= ys yl)
(tobool (ssep 
(sll yprm flted19 Anon4 Anon5)
(pto xprm (sref (ref val Anon3) (ref next q9) ))
(ll q9 n6)
) )
))
)

(assert (not 
(exists ((n7 Int)(flted20 Int)(Anon6 Int)(Anon7 Int))(and 
(= n7 n)
(= flted20 (+ m1 n))
(<= ys1 yl1)
(<= 0 m1)
(<= 0 n)
(tobool (ssep 
(sll yprm flted20 Anon6 Anon7)
(ll x n7)
) )
))
))

(check-sat)