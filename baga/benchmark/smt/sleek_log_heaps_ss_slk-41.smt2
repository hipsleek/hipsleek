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
































































































































































(declare-fun l3_1932 () node)
(declare-fun r3_1935 () node)
(declare-fun dprm () NUM)
(declare-fun v13prm () Int)
(declare-fun m2prm () Int)
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
(declare-fun m25_1929 () Int)
(declare-fun m24_1928 () Int)
(declare-fun m26_1930 () Int)
(declare-fun mx1 () Int)
(declare-fun mx15_1937 () Int)
(declare-fun mx14_1934 () Int)
(declare-fun d3_1931 () Int)
(declare-fun m23 () Int)
(declare-fun m27_1933 () Int)
(declare-fun m28_1936 () Int)


(assert 
(exists ((m24 Int)(m25 Int)(m26 Int)(d3 Int)(l3 node)(m27 Int)(mx14 Int)(r3 node)(m28 Int)(mx15 Int))(and 
;lexvar(= m2prm 0)
(= dprm d2)
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
(= m25 m28)
(= m24 m27)
(<= m26 1)
(<= 0 m26)
(= (+ m26 m28) m27)
(<= d3 mx1)
(<= mx15 d3)
(<= mx14 d3)
(<= 0 d3)
(= m23 (+ (+ m28 1) m27))
(tobool (ssep 
(pq l3 m24 mx14)
(pto lprm (sref (ref val d3) (ref nleft m27) (ref nright m28) (ref left l3) (ref right r3) ))
(pq r3 m25 mx15)
(pq r2 m22 mx2)
) )
))
)

(assert (not 
(and 
(tobool  
(pto lprm (sref (ref val val3prm) (ref nleft nleft3prm) (ref nright nright3prm) (ref left left3prm) (ref right right3prm) ))
 )
)
))

(check-sat)