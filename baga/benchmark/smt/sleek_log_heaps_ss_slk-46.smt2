(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun nleft () (Field node Int))
(declare-fun nright () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun pq ((?in node) (?n Int) (?mx Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)
(= ?mx 0)

)(exists ((?m1_28 Int)(?m2_29 Int)(?m3_27 Int))(and 
(= ?n (+ (+ ?m2 1) ?m1))
(<= 0 ?d)
(<= ?mx1 ?d)
(<= ?mx2 ?d)
(<= ?d ?mx)
(= (+ ?m3_27 ?m2) ?m1)
(<= 0 ?m3_27)
(<= ?m3_27 1)
(= ?m1_28 ?m1)
(= ?m2_29 ?m2)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref nleft ?m1) (ref nright ?m2) (ref left ?l) (ref right ?r) ))
(pq ?l ?m1_28 ?mx1)
(pq ?r ?m2_29 ?mx2)
) )
)))))
































































































































































(declare-fun l5_2276 () node)
(declare-fun r5_2279 () node)
(declare-fun dprm () NUM)
(declare-fun v13prm () Int)
(declare-fun lprm () node)
(declare-fun l2 () node)
(declare-fun rprm () node)
(declare-fun r2 () node)
(declare-fun mx2 () Int)
(declare-fun v12 () Int)
(declare-fun d2 () Int)
(declare-fun m1 () Int)
(declare-fun m22 () Int)
(declare-fun m2 () Int)
(declare-fun m1prm () Int)
(declare-fun m2prm () Int)
(declare-fun m35_2273 () Int)
(declare-fun m34_2272 () Int)
(declare-fun m36_2274 () Int)
(declare-fun mx1 () Int)
(declare-fun mx19_2281 () Int)
(declare-fun mx18_2278 () Int)
(declare-fun d6_2275 () Int)
(declare-fun m23 () Int)
(declare-fun m37_2277 () Int)
(declare-fun m38_2280 () Int)


(assert 
(exists ((m34 Int)(m35 Int)(m36 Int)(d6 Int)(l5 node)(m37 Int)(mx18 Int)(r5 node)(m38 Int)(mx19 Int))(and 
;lexvar(= dprm d2)
(= v13prm v12)
(= m1prm m1)
(= m2prm m2)
(= lprm l2)
(= rprm r2)
(<= (+ 0 m2) m1)
(<= m1 (+ 1 m2))
(<= mx1 d2)
(<= mx2 d2)
(<= 0 v12)
(<= v12 d2)
(= m23 m1)
(= m22 m2)
(distinct m1prm 0)
(distinct m2prm 0)
(= m35 m38)
(= m34 m37)
(<= m36 1)
(<= 0 m36)
(= (+ m36 m38) m37)
(<= d6 mx1)
(<= mx19 d6)
(<= mx18 d6)
(<= 0 d6)
(= m23 (+ (+ m38 1) m37))
(tobool (ssep 
(pq l5 m34 mx18)
(pto lprm (sref (ref val d6) (ref nleft m37) (ref nright m38) (ref left l5) (ref right r5) ))
(pq r5 m35 mx19)
(pq r2 m22 mx2)
) )
))
)

(assert (not 
(and 
(tobool  
(pto lprm (sref (ref val val6prm) (ref nleft nleft6prm) (ref nright nright6prm) (ref left left6prm) (ref right right6prm) ))
 )
)
))

(check-sat)