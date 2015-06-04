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
(declare-fun yprm () node)
(declare-fun ma6_2080 () Int)
(declare-fun mi6_2079 () Int)
(declare-fun Anon3 () Int)
(declare-fun flted17_2078 () Int)
(declare-fun lg () Int)
(declare-fun yl1 () NUM)
(declare-fun sm () Int)
(declare-fun ys1 () NUM)
(declare-fun n5 () Int)
(declare-fun m1 () Int)
(declare-fun x () node)
(declare-fun y1 () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun flted16 () Int)
(declare-fun n () Int)


(assert 
(exists ((flted17 Int)(mi6 Int)(ma6 Int))(and 
;lexvar(<= sm lg)
(<= 0 n5)
;eqmax;eqmin(= flted17 (+ 1 n5))
(<= ys1 yl1)
(<= 0 m1)
(= lg yl1)
(= sm ys1)
(= n5 m1)
(= xprm x)
(= y1 y)
(distinct xprm nil)
(= (+ flted16 1) n)
(tobool (ssep 
(ll q9 flted16)
(pto xprm (sref (ref val Anon3) (ref next q9) ))
(sll yprm flted17 mi6 ma6)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val16prm) (ref next next16prm) ))
 )
)
))

(check-sat)